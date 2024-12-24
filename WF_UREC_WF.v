Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_UREC_WF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm307612_spec.
Require Import thm309905_spec.
Require Import thm7_spec.
Lemma lem318406 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem318407 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem318408 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem318407 A B f) (@lem318406 A B f)). Qed.
Lemma lem318409 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem318408 A B f g). Qed.
Lemma lem318410 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem318481 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term4 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem318482 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term4 A lt2).
Proof. exact (@lem318481 A lt2). Qed.
Lemma lem318505 {A : Type'} (lt2 : type1402 A) : (term5 A lt2) = (term5 A lt2).
Proof. exact (eq_refl (term5 A lt2)). Qed.
Lemma lem318506 {A : Type'} (lt2 : type1402 A) : (term6 A lt2) = (term7 A lt2).
Proof. exact (MK_COMB (@lem318505 A lt2) (@lem318482 A lt2)). Qed.
Lemma lem318509 {A : Type'} (lt2 : type1402 A) : (term7 A lt2) = (term6 A lt2).
Proof. exact (SYM (@lem318506 A lt2)). Qed.
Lemma lem318510 {A : Type'} (lt2 : type1402 A) (h1 : term8 A lt2) : term8 A lt2.
Proof. exact (h1). Qed.
Lemma lem318511 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem318512 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term8 A lt2) : term10 A P lt2.
Proof. exact (@lem318510 A lt2 h1 (term11 A P lt2)). Qed.
Lemma lem318513 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term10 A P lt2) = (term12 A P lt2).
Proof. exact (eq_refl (term10 A P lt2)). Qed.
Lemma lem318514 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term8 A lt2) : term12 A P lt2.
Proof. exact (EQ_MP (@lem318513 A P lt2) (@lem318512 A P lt2 h1)). Qed.
Lemma lem318544 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318545 {A : Type'} (f : type672 A) (y : A -> Prop) : (term14 A f y) = (f y).
Proof. exact (@lem318544 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem318546 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term15 A P lt2 f) = (term16 A P lt2 f).
Proof. exact (@lem318545 A (term11 A P lt2) f). Qed.
Lemma lem318547 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (eq_refl (term16 A P lt2 f)). Qed.
Lemma lem318548 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term18 A P lt2) = (term11 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318547 A P lt2 f)). Qed.
Lemma lem318549 {A : Type'} (f : A -> Prop) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem318550 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term15 A P lt2 f) = (term16 A P lt2 f).
Proof. exact (MK_COMB (@lem318548 A P lt2) (@lem318549 A f)). Qed.
Lemma lem318551 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem318552 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term19 A P lt2 f) = (term20 A P lt2 f).
Proof. exact (MK_COMB (@lem318551 A) (@lem318550 A P lt2 f)). Qed.
Lemma lem318553 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (eq_refl (term16 A P lt2 f)). Qed.
Lemma lem318554 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : ((term15 A P lt2 f) = (term16 A P lt2 f)) = ((term16 A P lt2 f) = (term17 A P lt2 f)).
Proof. exact (MK_COMB (@lem318552 A P lt2 f) (@lem318553 A P lt2 f)). Qed.
Lemma lem318555 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (EQ_MP (@lem318554 A P lt2 f) (@lem318546 A P lt2 f)). Qed.
Lemma lem318564 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318565 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term21 A P lt2 f x) = (term22 A P lt2 f x).
Proof. exact (MK_COMB (@lem318555 A P lt2 f) (@lem318564 A x)). Qed.
Lemma lem318567 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318568 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem318567 A Prop f y). Qed.
Lemma lem318569 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term24 A P lt2 f x) = (term22 A P lt2 f x).
Proof. exact (@lem318568 A (term17 A P lt2 f) x). Qed.
Lemma lem318570 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term22 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (eq_refl (term22 A P lt2 f x)). Qed.
Lemma lem318571 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term26 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem318570 A P lt2 x f)). Qed.
Lemma lem318572 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318573 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term24 A P lt2 f x) = (term22 A P lt2 f x).
Proof. exact (MK_COMB (@lem318571 A P lt2 f) (@lem318572 A x)). Qed.
Lemma lem318574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem318575 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term27 A P lt2 f x) = (term28 A P lt2 f x).
Proof. exact (MK_COMB (@lem318574) (@lem318573 A P lt2 f x)). Qed.
Lemma lem318576 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term22 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (eq_refl (term22 A P lt2 f x)). Qed.
Lemma lem318577 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : ((term24 A P lt2 f x) = (term22 A P lt2 f x)) = ((term22 A P lt2 f x) = (term25 A P lt2 x f)).
Proof. exact (MK_COMB (@lem318575 A P lt2 f x) (@lem318576 A P lt2 x f)). Qed.
Lemma lem318578 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term22 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (EQ_MP (@lem318577 A P lt2 x f) (@lem318569 A P lt2 f x)). Qed.
Lemma lem318587 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term21 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (TRANS (@lem318565 A P lt2 f x) (@lem318578 A P lt2 x f)). Qed.
Lemma lem318588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem318589 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term29 A P lt2 f x) = (term30 A P lt2 x f).
Proof. exact (MK_COMB (@lem318588) (@lem318587 A P lt2 x f)). Qed.
Lemma lem318591 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318592 {A : Type'} (f : type672 A) (y : A -> Prop) : (term14 A f y) = (f y).
Proof. exact (@lem318591 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem318593 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term15 A P lt2 g) = (term16 A P lt2 g).
Proof. exact (@lem318592 A (term11 A P lt2) g). Qed.
Lemma lem318594 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (eq_refl (term16 A P lt2 f)). Qed.
Lemma lem318595 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term18 A P lt2) = (term11 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318594 A P lt2 f)). Qed.
Lemma lem318596 {A : Type'} (g : A -> Prop) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem318597 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term15 A P lt2 g) = (term16 A P lt2 g).
Proof. exact (MK_COMB (@lem318595 A P lt2) (@lem318596 A g)). Qed.
Lemma lem318598 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem318599 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term19 A P lt2 g) = (term20 A P lt2 g).
Proof. exact (MK_COMB (@lem318598 A) (@lem318597 A P lt2 g)). Qed.
Lemma lem318600 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term16 A P lt2 g) = (term17 A P lt2 g).
Proof. exact (eq_refl (term16 A P lt2 g)). Qed.
Lemma lem318601 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : ((term15 A P lt2 g) = (term16 A P lt2 g)) = ((term16 A P lt2 g) = (term17 A P lt2 g)).
Proof. exact (MK_COMB (@lem318599 A P lt2 g) (@lem318600 A P lt2 g)). Qed.
Lemma lem318602 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term16 A P lt2 g) = (term17 A P lt2 g).
Proof. exact (EQ_MP (@lem318601 A P lt2 g) (@lem318593 A P lt2 g)). Qed.
Lemma lem318611 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318612 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term21 A P lt2 g x) = (term22 A P lt2 g x).
Proof. exact (MK_COMB (@lem318602 A P lt2 g) (@lem318611 A x)). Qed.
Lemma lem318614 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318615 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem318614 A Prop f y). Qed.
Lemma lem318616 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term24 A P lt2 g x) = (term22 A P lt2 g x).
Proof. exact (@lem318615 A (term17 A P lt2 g) x). Qed.
Lemma lem318617 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term22 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (eq_refl (term22 A P lt2 g x)). Qed.
Lemma lem318618 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term26 A P lt2 g) = (term17 A P lt2 g).
Proof. exact (fun_ext (fun x : A => @lem318617 A P lt2 x g)). Qed.
Lemma lem318619 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318620 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term24 A P lt2 g x) = (term22 A P lt2 g x).
Proof. exact (MK_COMB (@lem318618 A P lt2 g) (@lem318619 A x)). Qed.
Lemma lem318621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem318622 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term27 A P lt2 g x) = (term28 A P lt2 g x).
Proof. exact (MK_COMB (@lem318621) (@lem318620 A P lt2 g x)). Qed.
Lemma lem318623 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term22 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (eq_refl (term22 A P lt2 g x)). Qed.
Lemma lem318624 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term24 A P lt2 g x) = (term22 A P lt2 g x)) = ((term22 A P lt2 g x) = (term25 A P lt2 x g)).
Proof. exact (MK_COMB (@lem318622 A P lt2 g x) (@lem318623 A P lt2 x g)). Qed.
Lemma lem318625 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term22 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (EQ_MP (@lem318624 A P lt2 x g) (@lem318616 A P lt2 g x)). Qed.
Lemma lem318634 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term21 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (TRANS (@lem318612 A P lt2 g x) (@lem318625 A P lt2 x g)). Qed.
Lemma lem318635 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term21 A P lt2 f x) = (term21 A P lt2 g x)) = ((term25 A P lt2 x f) = (term25 A P lt2 x g)).
Proof. exact (MK_COMB (@lem318589 A P lt2 x f) (@lem318634 A P lt2 x g)). Qed.
Lemma lem318638 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term31 A lt2 x f g) = (term31 A lt2 x f g).
Proof. exact (eq_refl (term31 A lt2 x f g)). Qed.
Lemma lem318639 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term32 A f P lt2 g x) = (term33 A f P lt2 x g).
Proof. exact (MK_COMB (@lem318638 A lt2 x f g) (@lem318635 A f P lt2 x g)). Qed.
Lemma lem318642 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term34 A f P lt2 g) = (term35 A f P lt2 g).
Proof. exact (fun_ext (fun x : A => @lem318639 A f P lt2 x g)). Qed.
Lemma lem318643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318644 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term36 A f P lt2 g) = (term37 A f P lt2 g).
Proof. exact (MK_COMB (@lem318643 A) (@lem318642 A f P lt2 g)). Qed.
Lemma lem318649 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) : (term38 A f P lt2) = (term39 A f P lt2).
Proof. exact (fun_ext (fun g : A -> Prop => @lem318644 A f P lt2 g)). Qed.
Lemma lem318650 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem318651 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) : (term40 A f P lt2) = (term41 A f P lt2).
Proof. exact (MK_COMB (@lem318650 A) (@lem318649 A f P lt2)). Qed.
Lemma lem318656 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term42 A P lt2) = (term43 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318651 A f P lt2)). Qed.
Lemma lem318657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem318658 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term44 A P lt2) = (term45 A P lt2).
Proof. exact (MK_COMB (@lem318657 A) (@lem318656 A P lt2)). Qed.
Lemma lem318663 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318664 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term46 A P lt2) = (term47 A P lt2).
Proof. exact (MK_COMB (@lem318663) (@lem318658 A P lt2)). Qed.
Lemma lem318684 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318685 {A : Type'} (f : type672 A) (y : A -> Prop) : (term14 A f y) = (f y).
Proof. exact (@lem318684 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem318686 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term15 A P lt2 f) = (term16 A P lt2 f).
Proof. exact (@lem318685 A (term11 A P lt2) f). Qed.
Lemma lem318687 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (eq_refl (term16 A P lt2 f)). Qed.
Lemma lem318688 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term18 A P lt2) = (term11 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318687 A P lt2 f)). Qed.
Lemma lem318689 {A : Type'} (f : A -> Prop) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem318690 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term15 A P lt2 f) = (term16 A P lt2 f).
Proof. exact (MK_COMB (@lem318688 A P lt2) (@lem318689 A f)). Qed.
Lemma lem318691 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem318692 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term19 A P lt2 f) = (term20 A P lt2 f).
Proof. exact (MK_COMB (@lem318691 A) (@lem318690 A P lt2 f)). Qed.
Lemma lem318693 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (eq_refl (term16 A P lt2 f)). Qed.
Lemma lem318694 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : ((term15 A P lt2 f) = (term16 A P lt2 f)) = ((term16 A P lt2 f) = (term17 A P lt2 f)).
Proof. exact (MK_COMB (@lem318692 A P lt2 f) (@lem318693 A P lt2 f)). Qed.
Lemma lem318695 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (EQ_MP (@lem318694 A P lt2 f) (@lem318686 A P lt2 f)). Qed.
Lemma lem318704 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318705 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term21 A P lt2 f x) = (term22 A P lt2 f x).
Proof. exact (MK_COMB (@lem318695 A P lt2 f) (@lem318704 A x)). Qed.
Lemma lem318707 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318708 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem318707 A Prop f y). Qed.
Lemma lem318709 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term24 A P lt2 f x) = (term22 A P lt2 f x).
Proof. exact (@lem318708 A (term17 A P lt2 f) x). Qed.
Lemma lem318710 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term22 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (eq_refl (term22 A P lt2 f x)). Qed.
Lemma lem318711 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term26 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem318710 A P lt2 x f)). Qed.
Lemma lem318712 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318713 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term24 A P lt2 f x) = (term22 A P lt2 f x).
Proof. exact (MK_COMB (@lem318711 A P lt2 f) (@lem318712 A x)). Qed.
Lemma lem318714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem318715 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (x : A) : (term27 A P lt2 f x) = (term28 A P lt2 f x).
Proof. exact (MK_COMB (@lem318714) (@lem318713 A P lt2 f x)). Qed.
Lemma lem318716 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term22 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (eq_refl (term22 A P lt2 f x)). Qed.
Lemma lem318717 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : ((term24 A P lt2 f x) = (term22 A P lt2 f x)) = ((term22 A P lt2 f x) = (term25 A P lt2 x f)).
Proof. exact (MK_COMB (@lem318715 A P lt2 f x) (@lem318716 A P lt2 x f)). Qed.
Lemma lem318718 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term22 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (EQ_MP (@lem318717 A P lt2 x f) (@lem318709 A P lt2 f x)). Qed.
Lemma lem318727 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term21 A P lt2 f x) = (term25 A P lt2 x f).
Proof. exact (TRANS (@lem318705 A P lt2 f x) (@lem318718 A P lt2 x f)). Qed.
Lemma lem318728 {A : Type'} (f : A -> Prop) (x : A) : (term48 A f x) = (term48 A f x).
Proof. exact (eq_refl (term48 A f x)). Qed.
Lemma lem318729 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : ((f x) = (term21 A P lt2 f x)) = ((f x) = (term25 A P lt2 x f)).
Proof. exact (MK_COMB (@lem318728 A f x) (@lem318727 A P lt2 x f)). Qed.
Lemma lem318732 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term49 A P lt2 f) = (term50 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem318729 A P lt2 x f)). Qed.
Lemma lem318733 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318734 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term51 A P lt2 f) = (term52 A P lt2 f).
Proof. exact (MK_COMB (@lem318733 A) (@lem318732 A P lt2 f)). Qed.
Lemma lem318739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem318740 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term53 A P lt2 f) = (term54 A P lt2 f).
Proof. exact (MK_COMB (@lem318739) (@lem318734 A P lt2 f)). Qed.
Lemma lem318748 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318749 {A : Type'} (f : type672 A) (y : A -> Prop) : (term14 A f y) = (f y).
Proof. exact (@lem318748 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem318750 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term15 A P lt2 g) = (term16 A P lt2 g).
Proof. exact (@lem318749 A (term11 A P lt2) g). Qed.
Lemma lem318751 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term16 A P lt2 f) = (term17 A P lt2 f).
Proof. exact (eq_refl (term16 A P lt2 f)). Qed.
Lemma lem318752 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term18 A P lt2) = (term11 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318751 A P lt2 f)). Qed.
Lemma lem318753 {A : Type'} (g : A -> Prop) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem318754 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term15 A P lt2 g) = (term16 A P lt2 g).
Proof. exact (MK_COMB (@lem318752 A P lt2) (@lem318753 A g)). Qed.
Lemma lem318755 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem318756 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term19 A P lt2 g) = (term20 A P lt2 g).
Proof. exact (MK_COMB (@lem318755 A) (@lem318754 A P lt2 g)). Qed.
Lemma lem318757 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term16 A P lt2 g) = (term17 A P lt2 g).
Proof. exact (eq_refl (term16 A P lt2 g)). Qed.
Lemma lem318758 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : ((term15 A P lt2 g) = (term16 A P lt2 g)) = ((term16 A P lt2 g) = (term17 A P lt2 g)).
Proof. exact (MK_COMB (@lem318756 A P lt2 g) (@lem318757 A P lt2 g)). Qed.
Lemma lem318759 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term16 A P lt2 g) = (term17 A P lt2 g).
Proof. exact (EQ_MP (@lem318758 A P lt2 g) (@lem318750 A P lt2 g)). Qed.
Lemma lem318768 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318769 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term21 A P lt2 g x) = (term22 A P lt2 g x).
Proof. exact (MK_COMB (@lem318759 A P lt2 g) (@lem318768 A x)). Qed.
Lemma lem318771 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem318772 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem318771 A Prop f y). Qed.
Lemma lem318773 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term24 A P lt2 g x) = (term22 A P lt2 g x).
Proof. exact (@lem318772 A (term17 A P lt2 g) x). Qed.
Lemma lem318774 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term22 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (eq_refl (term22 A P lt2 g x)). Qed.
Lemma lem318775 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term26 A P lt2 g) = (term17 A P lt2 g).
Proof. exact (fun_ext (fun x : A => @lem318774 A P lt2 x g)). Qed.
Lemma lem318776 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem318777 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term24 A P lt2 g x) = (term22 A P lt2 g x).
Proof. exact (MK_COMB (@lem318775 A P lt2 g) (@lem318776 A x)). Qed.
Lemma lem318778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem318779 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) (x : A) : (term27 A P lt2 g x) = (term28 A P lt2 g x).
Proof. exact (MK_COMB (@lem318778) (@lem318777 A P lt2 g x)). Qed.
Lemma lem318780 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term22 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (eq_refl (term22 A P lt2 g x)). Qed.
Lemma lem318781 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term24 A P lt2 g x) = (term22 A P lt2 g x)) = ((term22 A P lt2 g x) = (term25 A P lt2 x g)).
Proof. exact (MK_COMB (@lem318779 A P lt2 g x) (@lem318780 A P lt2 x g)). Qed.
Lemma lem318782 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term22 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (EQ_MP (@lem318781 A P lt2 x g) (@lem318773 A P lt2 g x)). Qed.
Lemma lem318791 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term21 A P lt2 g x) = (term25 A P lt2 x g).
Proof. exact (TRANS (@lem318769 A P lt2 g x) (@lem318782 A P lt2 x g)). Qed.
Lemma lem318792 {A : Type'} (g : A -> Prop) (x : A) : (term48 A g x) = (term48 A g x).
Proof. exact (eq_refl (term48 A g x)). Qed.
Lemma lem318793 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((g x) = (term21 A P lt2 g x)) = ((g x) = (term25 A P lt2 x g)).
Proof. exact (MK_COMB (@lem318792 A g x) (@lem318791 A P lt2 x g)). Qed.
Lemma lem318796 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term49 A P lt2 g) = (term50 A P lt2 g).
Proof. exact (fun_ext (fun x : A => @lem318793 A P lt2 x g)). Qed.
Lemma lem318797 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318798 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term51 A P lt2 g) = (term52 A P lt2 g).
Proof. exact (MK_COMB (@lem318797 A) (@lem318796 A P lt2 g)). Qed.
Lemma lem318803 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term55 A f P lt2 g) = (term56 A f P lt2 g).
Proof. exact (MK_COMB (@lem318740 A P lt2 f) (@lem318798 A P lt2 g)). Qed.
Lemma lem318806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318807 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term57 A f P lt2 g) = (term58 A f P lt2 g).
Proof. exact (MK_COMB (@lem318806) (@lem318803 A f P lt2 g)). Qed.
Lemma lem318810 {A : Type'} (f : A -> Prop) (g : A -> Prop) : (f = g) = (f = g).
Proof. exact (eq_refl (f = g)). Qed.
Lemma lem318811 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) (g : A -> Prop) : (term59 A P lt2 f g) = (term60 A P lt2 f g).
Proof. exact (MK_COMB (@lem318807 A f P lt2 g) (@lem318810 A f g)). Qed.
Lemma lem318814 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term61 A P lt2 f) = (term62 A P lt2 f).
Proof. exact (fun_ext (fun g : A -> Prop => @lem318811 A P lt2 f g)). Qed.
Lemma lem318815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem318816 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> Prop) : (term63 A P lt2 f) = (term64 A P lt2 f).
Proof. exact (MK_COMB (@lem318815 A) (@lem318814 A P lt2 f)). Qed.
Lemma lem318821 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term65 A P lt2) = (term66 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318816 A P lt2 f)). Qed.
Lemma lem318822 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem318823 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term67 A P lt2) = (term68 A P lt2).
Proof. exact (MK_COMB (@lem318822 A) (@lem318821 A P lt2)). Qed.
Lemma lem318828 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term12 A P lt2) = (term69 A P lt2).
Proof. exact (MK_COMB (@lem318664 A P lt2) (@lem318823 A P lt2)). Qed.
Lemma lem318831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318832 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term70 A P lt2) = (term71 A P lt2).
Proof. exact (MK_COMB (@lem318831) (@lem318828 A P lt2)). Qed.
Lemma lem318837 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem318838 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term74 A lt2 P).
Proof. exact (MK_COMB (@lem318832 A P lt2) (@lem318837 A P)). Qed.
Lemma lem318841 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term73 A lt2 P).
Proof. exact (SYM (@lem318838 A lt2 P)). Qed.
Lemma lem318842 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term45 A P lt2.
Proof. exact (h1). Qed.
Lemma lem318843 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term75 A P lt2 f.
Proof. exact (@lem318842 A P lt2 h1 f). Qed.
Lemma lem318844 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) : (term75 A P lt2 f) = (term41 A f P lt2).
Proof. exact (eq_refl (term75 A P lt2 f)). Qed.
Lemma lem318845 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term41 A f P lt2.
Proof. exact (EQ_MP (@lem318844 A f P lt2) (@lem318843 A f P lt2 h1)). Qed.
Lemma lem318846 {A : Type'} (f : A -> Prop) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term76 A f P lt2 g.
Proof. exact (@lem318845 A f P lt2 h1 g). Qed.
Lemma lem318847 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term76 A f P lt2 g) = (term37 A f P lt2 g).
Proof. exact (eq_refl (term76 A f P lt2 g)). Qed.
Lemma lem318848 {A : Type'} (f : A -> Prop) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term37 A f P lt2 g.
Proof. exact (EQ_MP (@lem318847 A f P lt2 g) (@lem318846 A f g P lt2 h1)). Qed.
Lemma lem318849 {A : Type'} (f : A -> Prop) (g : A -> Prop) (x : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term77 A f P lt2 g x.
Proof. exact (@lem318848 A f g P lt2 h1 x). Qed.
Lemma lem318850 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term77 A f P lt2 g x) = (term33 A f P lt2 x g).
Proof. exact (eq_refl (term77 A f P lt2 g x)). Qed.
Lemma lem318851 {A : Type'} (f : A -> Prop) (x : A) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : term33 A f P lt2 x g.
Proof. exact (EQ_MP (@lem318850 A f P lt2 x g) (@lem318849 A f g x P lt2 h1)). Qed.
Lemma lem318852 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term33 A f P lt2 x g) = ((term33 A f P lt2 x g) = True).
Proof. exact (@lem7 (term33 A f P lt2 x g)). Qed.
Lemma lem318871 {A : Type'} (f : A -> Prop) (x : A) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term33 A f P lt2 x g) = True.
Proof. exact (EQ_MP (@lem318852 A f P lt2 x g) (@lem318851 A f x g P lt2 h1)). Qed.
Lemma lem318872 {A : Type'} (f : A -> Prop) (x : A) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term33 A f P lt2 x g) = True.
Proof. exact (@lem318871 A f x g P lt2 h1). Qed.
Lemma lem318873 {A : Type'} (f : A -> Prop) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term35 A f P lt2 g) = (term78 A).
Proof. exact (fun_ext (fun x : A => @lem318872 A f x g P lt2 h1)). Qed.
Lemma lem318874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem318875 {A : Type'} (f : A -> Prop) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term37 A f P lt2 g) = (term79 A).
Proof. exact (MK_COMB (@lem318874 A) (@lem318873 A f g P lt2 h1)). Qed.
Lemma lem318877 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem318878 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (@lem318877 A t). Qed.
Lemma lem318879 {A : Type'} : (term79 A) = True.
Proof. exact (@lem318878 A True). Qed.
Lemma lem318880 {A : Type'} (f : A -> Prop) (g : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term37 A f P lt2 g) = True.
Proof. exact (TRANS (@lem318875 A f g P lt2 h1) (@lem318879 A)). Qed.
Lemma lem318881 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term39 A f P lt2) = (term81 A).
Proof. exact (fun_ext (fun g : A -> Prop => @lem318880 A f g P lt2 h1)). Qed.
Lemma lem318882 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem318883 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term41 A f P lt2) = (term82 A).
Proof. exact (MK_COMB (@lem318882 A) (@lem318881 A f P lt2 h1)). Qed.
Lemma lem318885 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem318886 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (@lem318885 (A -> Prop) t). Qed.
Lemma lem318887 {A : Type'} : (term82 A) = True.
Proof. exact (@lem318886 A True). Qed.
Lemma lem318888 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term41 A f P lt2) = True.
Proof. exact (TRANS (@lem318883 A f P lt2 h1) (@lem318887 A)). Qed.
Lemma lem318889 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term43 A P lt2) = (term81 A).
Proof. exact (fun_ext (fun f : A -> Prop => @lem318888 A f P lt2 h1)). Qed.
Lemma lem318890 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem318891 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term45 A P lt2) = (term82 A).
Proof. exact (MK_COMB (@lem318890 A) (@lem318889 A P lt2 h1)). Qed.
Lemma lem318893 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem318894 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (@lem318893 (A -> Prop) t). Qed.
Lemma lem318895 {A : Type'} : (term82 A) = True.
Proof. exact (@lem318894 A True). Qed.
Lemma lem318896 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term45 A P lt2) = True.
Proof. exact (TRANS (@lem318891 A P lt2 h1) (@lem318895 A)). Qed.
Lemma lem318897 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318898 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term47 A P lt2) = (imp True).
Proof. exact (MK_COMB (@lem318897) (@lem318896 A P lt2 h1)). Qed.
Lemma lem318941 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term68 A P lt2) = (term68 A P lt2).
Proof. exact (eq_refl (term68 A P lt2)). Qed.
Lemma lem318942 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term69 A P lt2) = (term84 A P lt2).
Proof. exact (MK_COMB (@lem318898 A P lt2 h1) (@lem318941 A P lt2)). Qed.
Lemma lem318944 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem318945 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term84 A P lt2) = (term68 A P lt2).
Proof. exact (@lem318944 (term68 A P lt2)). Qed.
Lemma lem318988 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term69 A P lt2) = (term68 A P lt2).
Proof. exact (TRANS (@lem318942 A P lt2 h1) (@lem318945 A P lt2)). Qed.
Lemma lem318989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem318990 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term71 A P lt2) = (term85 A P lt2).
Proof. exact (MK_COMB (@lem318989) (@lem318988 A P lt2 h1)). Qed.
Lemma lem318995 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem318996 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term74 A lt2 P) = (term86 A lt2 P).
Proof. exact (MK_COMB (@lem318990 A P lt2 h1) (@lem318995 A P)). Qed.
Lemma lem318999 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term45 A P lt2) : (term86 A lt2 P) = (term74 A lt2 P).
Proof. exact (SYM (@lem318996 A P lt2 h1)). Qed.
Lemma lem319001 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem319002 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term45 A P lt2) = (term88 A P lt2).
Proof. exact (@lem319001 (term45 A P lt2)). Qed.
Lemma lem319003 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term88 A P lt2) = (term45 A P lt2).
Proof. exact (SYM (@lem319002 A P lt2)). Qed.
Lemma lem319004 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term89 A P lt2) : term89 A P lt2.
Proof. exact (h1). Qed.
Lemma lem319007 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term88 A P lt2) : term88 A P lt2.
Proof. exact (h1). Qed.
Lemma lem319008 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term90 A P lt2.
Proof. exact (fun h0 : term88 A P lt2 => @lem319007 A P lt2 h0). Qed.
Lemma lem319009 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term90 A P lt2) : term90 A P lt2.
Proof. exact (h1). Qed.
Lemma lem319010 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term88 A P lt2) : term88 A P lt2.
Proof. exact (h1). Qed.
Lemma lem319011 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term88 A P lt2) (h2 : term90 A P lt2) : term88 A P lt2.
Proof. exact (@lem319009 A P lt2 h2 (@lem319010 A P lt2 h1)). Qed.
Lemma lem319012 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term88 A P lt2) : term91 A P lt2.
Proof. exact (fun h0 : term90 A P lt2 => @lem319011 A P lt2 h1 h0). Qed.
Lemma lem319013 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term90 A P lt2) : term90 A P lt2.
Proof. exact (h1). Qed.
Lemma lem319014 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term88 A P lt2) (h2 : term90 A P lt2) : term88 A P lt2.
Proof. exact (@lem319012 A P lt2 h1 (@lem319013 A P lt2 h2)). Qed.
Lemma lem319015 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term90 A P lt2) : term90 A P lt2.
Proof. exact (fun h0 : term88 A P lt2 => @lem319014 A P lt2 h0 h1). Qed.
Lemma lem319016 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term92 A P lt2.
Proof. exact (fun h0 : term90 A P lt2 => @lem319015 A P lt2 h0). Qed.
Lemma lem319019 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term90 A P lt2.
Proof. exact (@lem319016 A P lt2 (@lem319008 A P lt2)). Qed.
Lemma lem319020 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term90 A P lt2.
Proof. exact (@lem319019 A P lt2). Qed.
Lemma lem319030 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem319031 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term88 A P lt2) = (term93 A P lt2).
Proof. exact (@lem319030 (term89 A P lt2)). Qed.
Lemma lem319033 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem319034 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term93 A P lt2) = (term45 A P lt2).
Proof. exact (@lem319033 (term45 A P lt2)). Qed.
Lemma lem319039 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term88 A P lt2) = (term45 A P lt2).
Proof. exact (TRANS (@lem319031 A P lt2) (@lem319034 A P lt2)). Qed.
Lemma lem319072 {A : Type'} (lt2 : type1402 A) : (term95 A lt2) = (term96 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem319039 A P lt2)). Qed.
Lemma lem319073 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem319074 {A : Type'} (lt2 : type1402 A) : (term97 A lt2) = (term98 A lt2).
Proof. exact (MK_COMB (@lem319073 A) (@lem319072 A lt2)). Qed.
Lemma lem319079 {A : Type'} : (term99 A) = (term100 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem319074 A lt2)). Qed.
Lemma lem319080 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem319089 {A : Type'} : (term101 A) = (term102 A).
Proof. exact (MK_COMB (@lem319080 A) (@lem319079 A)). Qed.
Lemma lem319094 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term103 A lt2 x g z) = (term103 A lt2 x g z).
Proof. exact (eq_refl (term103 A lt2 x g z)). Qed.
Lemma lem319095 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term104 A lt2 x g) = (term104 A lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319094 A lt2 x g z)). Qed.
Lemma lem319096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319097 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term105 A lt2 x g) = (term105 A lt2 x g).
Proof. exact (MK_COMB (@lem319096 A) (@lem319095 A lt2 x g)). Qed.
Lemma lem319100 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem319101 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term25 A P lt2 x g) = (term25 A P lt2 x g).
Proof. exact (MK_COMB (@lem319100 A P x) (@lem319097 A lt2 x g)). Qed.
Lemma lem319106 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term103 A lt2 x f z) = (term103 A lt2 x f z).
Proof. exact (eq_refl (term103 A lt2 x f z)). Qed.
Lemma lem319107 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term104 A lt2 x f) = (term104 A lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319106 A lt2 x f z)). Qed.
Lemma lem319108 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319109 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term105 A lt2 x f) = (term105 A lt2 x f).
Proof. exact (MK_COMB (@lem319108 A) (@lem319107 A lt2 x f)). Qed.
Lemma lem319112 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem319113 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term25 A P lt2 x f) = (term25 A P lt2 x f).
Proof. exact (MK_COMB (@lem319112 A P x) (@lem319109 A lt2 x f)). Qed.
Lemma lem319114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem319115 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term30 A P lt2 x f) = (term30 A P lt2 x f).
Proof. exact (MK_COMB (@lem319114) (@lem319113 A P lt2 x f)). Qed.
Lemma lem319116 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term25 A P lt2 x f) = (term25 A P lt2 x g)) = ((term25 A P lt2 x f) = (term25 A P lt2 x g)).
Proof. exact (MK_COMB (@lem319115 A P lt2 x f) (@lem319101 A P lt2 x g)). Qed.
Lemma lem319125 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term107 A lt2 x f g z) = (term107 A lt2 x f g z).
Proof. exact (eq_refl (term107 A lt2 x f g z)). Qed.
Lemma lem319126 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term108 A lt2 x f g) = (term108 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem319125 A lt2 x f g z)). Qed.
Lemma lem319127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319128 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term109 A lt2 x f g) = (term109 A lt2 x f g).
Proof. exact (MK_COMB (@lem319127 A) (@lem319126 A lt2 x f g)). Qed.
Lemma lem319129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem319130 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term31 A lt2 x f g) = (term31 A lt2 x f g).
Proof. exact (MK_COMB (@lem319129) (@lem319128 A lt2 x f g)). Qed.
Lemma lem319131 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term33 A f P lt2 x g) = (term33 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319130 A lt2 x f g) (@lem319116 A f P lt2 x g)). Qed.
Lemma lem319132 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term35 A f P lt2 g) = (term35 A f P lt2 g).
Proof. exact (fun_ext (fun x : A => @lem319131 A f P lt2 x g)). Qed.
Lemma lem319133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319134 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : (term37 A f P lt2 g) = (term37 A f P lt2 g).
Proof. exact (MK_COMB (@lem319133 A) (@lem319132 A f P lt2 g)). Qed.
Lemma lem319135 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) : (term39 A f P lt2) = (term39 A f P lt2).
Proof. exact (fun_ext (fun g : A -> Prop => @lem319134 A f P lt2 g)). Qed.
Lemma lem319136 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem319137 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) : (term41 A f P lt2) = (term41 A f P lt2).
Proof. exact (MK_COMB (@lem319136 A) (@lem319135 A f P lt2)). Qed.
Lemma lem319138 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term43 A P lt2) = (term43 A P lt2).
Proof. exact (fun_ext (fun f : A -> Prop => @lem319137 A f P lt2)). Qed.
Lemma lem319139 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem319140 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term45 A P lt2) = (term45 A P lt2).
Proof. exact (MK_COMB (@lem319139 A) (@lem319138 A P lt2)). Qed.
Lemma lem319141 {A : Type'} (lt2 : type1402 A) : (term96 A lt2) = (term96 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem319140 A P lt2)). Qed.
Lemma lem319142 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem319143 {A : Type'} (lt2 : type1402 A) : (term98 A lt2) = (term98 A lt2).
Proof. exact (MK_COMB (@lem319142 A) (@lem319141 A lt2)). Qed.
Lemma lem319144 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem319143 A lt2)). Qed.
Lemma lem319145 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem319146 {A : Type'} : (term102 A) = (term102 A).
Proof. exact (MK_COMB (@lem319145 A) (@lem319144 A)). Qed.
Lemma lem319209 {A : Type'} : (term101 A) = (term102 A).
Proof. exact (TRANS (@lem319089 A) (@lem319146 A)). Qed.
Lemma lem319210 {A : Type'} : (term102 A) = (term101 A).
Proof. exact (SYM (@lem319209 A)). Qed.
Lemma lem319211 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term109 A lt2 x f g.
Proof. exact (h1). Qed.
Lemma lem319213 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem319214 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term25 A P lt2 x f) = (term25 A P lt2 x g)) = (term110 A f P lt2 x g).
Proof. exact (@lem319213 ((term25 A P lt2 x f) = (term25 A P lt2 x g))). Qed.
Lemma lem319215 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term110 A f P lt2 x g) = ((term25 A P lt2 x f) = (term25 A P lt2 x g)).
Proof. exact (SYM (@lem319214 A f P lt2 x g)). Qed.
Lemma lem319216 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term111 A f P lt2 x g) : term111 A f P lt2 x g.
Proof. exact (h1). Qed.
Lemma lem319232 {A : Type'} (f : A -> Prop) (g : A -> Prop) (z : A) : ((f z) = (g z)) = (term112 A f g z).
Proof. exact (@lem17784 (f z) (g z)). Qed.
Lemma lem319234 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term113 A lt2 z x) = (term113 A lt2 z x).
Proof. exact (eq_refl (term113 A lt2 z x)). Qed.
Lemma lem319235 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term114 A lt2 x f g z) = (term115 A lt2 x f g z).
Proof. exact (MK_COMB (@lem319234 A lt2 z x) (@lem319232 A f g z)). Qed.
Lemma lem319236 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term107 A lt2 x f g z) = (term114 A lt2 x f g z).
Proof. exact (@lem17265 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem319237 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term107 A lt2 x f g z) = (term115 A lt2 x f g z).
Proof. exact (TRANS (@lem319236 A lt2 x f g z) (@lem319235 A lt2 x f g z)). Qed.
Lemma lem319238 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term108 A lt2 x f g) = (term116 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem319237 A lt2 x f g z)). Qed.
Lemma lem319239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319292 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term109 A lt2 x f g) = (term117 A lt2 x f g).
Proof. exact (MK_COMB (@lem319239 A) (@lem319238 A lt2 x f g)). Qed.
Lemma lem319293 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term117 A lt2 x f g.
Proof. exact (EQ_MP (@lem319292 A lt2 x f g) (@lem319211 A lt2 x f g h1)). Qed.
Lemma lem319304 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term118 A lt2 x f z) = (term119 A lt2 x f z).
Proof. exact (@lem17362 (lt2 z x) (f z)). Qed.
Lemma lem319309 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term103 A lt2 x f z) = (term120 A lt2 x f z).
Proof. exact (@lem17265 (lt2 z x) (f z)). Qed.
Lemma lem319310 {A : Type'} (P : A -> Prop) : (term121 A P) = (term122 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem319311 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term123 A lt2 x f) = (term124 A lt2 x f).
Proof. exact (@lem319310 A (term104 A lt2 x f)). Qed.
Lemma lem319312 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term125 A lt2 x f z) = (term103 A lt2 x f z).
Proof. exact (eq_refl (term125 A lt2 x f z)). Qed.
Lemma lem319313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem319314 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term126 A lt2 x f z) = (term118 A lt2 x f z).
Proof. exact (MK_COMB (@lem319313) (@lem319312 A lt2 x f z)). Qed.
Lemma lem319315 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term126 A lt2 x f z) = (term119 A lt2 x f z).
Proof. exact (TRANS (@lem319314 A lt2 x f z) (@lem319304 A lt2 x f z)). Qed.
Lemma lem319316 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term127 A lt2 x f) = (term128 A lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319315 A lt2 x f z)). Qed.
Lemma lem319317 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319318 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term124 A lt2 x f) = (term129 A lt2 x f).
Proof. exact (MK_COMB (@lem319317 A) (@lem319316 A lt2 x f)). Qed.
Lemma lem319319 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term123 A lt2 x f) = (term129 A lt2 x f).
Proof. exact (TRANS (@lem319311 A lt2 x f) (@lem319318 A lt2 x f)). Qed.
Lemma lem319320 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term104 A lt2 x f) = (term130 A lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319309 A lt2 x f z)). Qed.
Lemma lem319321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319322 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term105 A lt2 x f) = (term131 A lt2 x f).
Proof. exact (MK_COMB (@lem319321 A) (@lem319320 A lt2 x f)). Qed.
Lemma lem319324 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem319325 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term133 A P lt2 x f) = (term134 A P lt2 x f).
Proof. exact (MK_COMB (@lem319324 A P x) (@lem319319 A lt2 x f)). Qed.
Lemma lem319326 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term135 A P lt2 x f) = (term133 A P lt2 x f).
Proof. exact (@lem17160 (P x) (term105 A lt2 x f)). Qed.
Lemma lem319327 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term135 A P lt2 x f) = (term134 A P lt2 x f).
Proof. exact (TRANS (@lem319326 A P lt2 x f) (@lem319325 A P lt2 x f)). Qed.
Lemma lem319329 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem319330 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term25 A P lt2 x f) = (term136 A P lt2 x f).
Proof. exact (MK_COMB (@lem319329 A P x) (@lem319322 A lt2 x f)). Qed.
Lemma lem319341 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term118 A lt2 x g z) = (term119 A lt2 x g z).
Proof. exact (@lem17362 (lt2 z x) (g z)). Qed.
Lemma lem319346 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term103 A lt2 x g z) = (term120 A lt2 x g z).
Proof. exact (@lem17265 (lt2 z x) (g z)). Qed.
Lemma lem319347 {A : Type'} (P : A -> Prop) : (term121 A P) = (term122 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem319348 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term123 A lt2 x g) = (term124 A lt2 x g).
Proof. exact (@lem319347 A (term104 A lt2 x g)). Qed.
Lemma lem319349 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term125 A lt2 x g z) = (term103 A lt2 x g z).
Proof. exact (eq_refl (term125 A lt2 x g z)). Qed.
Lemma lem319350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem319351 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term126 A lt2 x g z) = (term118 A lt2 x g z).
Proof. exact (MK_COMB (@lem319350) (@lem319349 A lt2 x g z)). Qed.
Lemma lem319352 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term126 A lt2 x g z) = (term119 A lt2 x g z).
Proof. exact (TRANS (@lem319351 A lt2 x g z) (@lem319341 A lt2 x g z)). Qed.
Lemma lem319353 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term127 A lt2 x g) = (term128 A lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319352 A lt2 x g z)). Qed.
Lemma lem319354 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319355 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term124 A lt2 x g) = (term129 A lt2 x g).
Proof. exact (MK_COMB (@lem319354 A) (@lem319353 A lt2 x g)). Qed.
Lemma lem319356 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term123 A lt2 x g) = (term129 A lt2 x g).
Proof. exact (TRANS (@lem319348 A lt2 x g) (@lem319355 A lt2 x g)). Qed.
Lemma lem319357 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term104 A lt2 x g) = (term130 A lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319346 A lt2 x g z)). Qed.
Lemma lem319358 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319359 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term105 A lt2 x g) = (term131 A lt2 x g).
Proof. exact (MK_COMB (@lem319358 A) (@lem319357 A lt2 x g)). Qed.
Lemma lem319361 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem319362 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term133 A P lt2 x g) = (term134 A P lt2 x g).
Proof. exact (MK_COMB (@lem319361 A P x) (@lem319356 A lt2 x g)). Qed.
Lemma lem319363 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term135 A P lt2 x g) = (term133 A P lt2 x g).
Proof. exact (@lem17160 (P x) (term105 A lt2 x g)). Qed.
Lemma lem319364 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term135 A P lt2 x g) = (term134 A P lt2 x g).
Proof. exact (TRANS (@lem319363 A P lt2 x g) (@lem319362 A P lt2 x g)). Qed.
Lemma lem319366 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem319367 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term25 A P lt2 x g) = (term136 A P lt2 x g).
Proof. exact (MK_COMB (@lem319366 A P x) (@lem319359 A lt2 x g)). Qed.
Lemma lem319368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem319369 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term137 A P lt2 x f) = (term138 A P lt2 x f).
Proof. exact (MK_COMB (@lem319368) (@lem319327 A P lt2 x f)). Qed.
Lemma lem319370 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term139 A f P lt2 x g) = (term140 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319369 A P lt2 x f) (@lem319367 A P lt2 x g)). Qed.
Lemma lem319371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem319372 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term141 A P lt2 x f) = (term142 A P lt2 x f).
Proof. exact (MK_COMB (@lem319371) (@lem319330 A P lt2 x f)). Qed.
Lemma lem319373 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term143 A f P lt2 x g) = (term144 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319372 A P lt2 x f) (@lem319364 A P lt2 x g)). Qed.
Lemma lem319374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem319375 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term145 A f P lt2 x g) = (term146 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319374) (@lem319373 A f P lt2 x g)). Qed.
Lemma lem319376 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term147 A f P lt2 x g) = (term148 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319375 A f P lt2 x g) (@lem319370 A f P lt2 x g)). Qed.
Lemma lem319377 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term111 A f P lt2 x g) = (term147 A f P lt2 x g).
Proof. exact (@lem17646 (term25 A P lt2 x f) (term25 A P lt2 x g)). Qed.
Lemma lem319378 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term111 A f P lt2 x g) = (term148 A f P lt2 x g).
Proof. exact (TRANS (@lem319377 A f P lt2 x g) (@lem319376 A f P lt2 x g)). Qed.
Lemma lem319541 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem319542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem319541 A P Q). Qed.
Lemma lem319543 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term151 A P lt2 x g) = (term152 A P lt2 x g).
Proof. exact (@lem319542 A (term153 A P x) (term128 A lt2 x g)). Qed.
Lemma lem319544 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term154 A lt2 x g z) = (term119 A lt2 x g z).
Proof. exact (eq_refl (term154 A lt2 x g z)). Qed.
Lemma lem319545 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term155 A lt2 x g) = (term128 A lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319544 A lt2 x g z)). Qed.
Lemma lem319546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319547 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term156 A lt2 x g) = (term129 A lt2 x g).
Proof. exact (MK_COMB (@lem319546 A) (@lem319545 A lt2 x g)). Qed.
Lemma lem319548 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem319549 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term151 A P lt2 x g) = (term134 A P lt2 x g).
Proof. exact (MK_COMB (@lem319548 A P x) (@lem319547 A lt2 x g)). Qed.
Lemma lem319550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem319551 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term157 A P lt2 x g) = (term158 A P lt2 x g).
Proof. exact (MK_COMB (@lem319550) (@lem319549 A P lt2 x g)). Qed.
Lemma lem319552 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term154 A lt2 x g z) = (term119 A lt2 x g z).
Proof. exact (eq_refl (term154 A lt2 x g z)). Qed.
Lemma lem319553 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem319554 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term159 A P lt2 x g z) = (term160 A P lt2 x g z).
Proof. exact (MK_COMB (@lem319553 A P x) (@lem319552 A lt2 x g z)). Qed.
Lemma lem319555 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term161 A P lt2 x g) = (term162 A P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319554 A P lt2 x g z)). Qed.
Lemma lem319556 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319557 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term152 A P lt2 x g) = (term163 A P lt2 x g).
Proof. exact (MK_COMB (@lem319556 A) (@lem319555 A P lt2 x g)). Qed.
Lemma lem319558 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term151 A P lt2 x g) = (term152 A P lt2 x g)) = ((term134 A P lt2 x g) = (term163 A P lt2 x g)).
Proof. exact (MK_COMB (@lem319551 A P lt2 x g) (@lem319557 A P lt2 x g)). Qed.
Lemma lem319559 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term134 A P lt2 x g) = (term163 A P lt2 x g).
Proof. exact (EQ_MP (@lem319558 A P lt2 x g) (@lem319543 A P lt2 x g)). Qed.
Lemma lem319560 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term142 A P lt2 x f) = (term142 A P lt2 x f).
Proof. exact (eq_refl (term142 A P lt2 x f)). Qed.
Lemma lem319561 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term144 A f P lt2 x g) = (term164 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319560 A P lt2 x f) (@lem319559 A P lt2 x g)). Qed.
Lemma lem319563 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem319564 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem319563 A P Q). Qed.
Lemma lem319565 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term165 A f P lt2 x g) = (term166 A f P lt2 x g).
Proof. exact (@lem319564 A (term136 A P lt2 x f) (term162 A P lt2 x g)). Qed.
Lemma lem319566 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term167 A P lt2 x g z) = (term160 A P lt2 x g z).
Proof. exact (eq_refl (term167 A P lt2 x g z)). Qed.
Lemma lem319567 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term168 A P lt2 x g) = (term162 A P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319566 A P lt2 x g z)). Qed.
Lemma lem319568 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319569 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term169 A P lt2 x g) = (term163 A P lt2 x g).
Proof. exact (MK_COMB (@lem319568 A) (@lem319567 A P lt2 x g)). Qed.
Lemma lem319570 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term142 A P lt2 x f) = (term142 A P lt2 x f).
Proof. exact (eq_refl (term142 A P lt2 x f)). Qed.
Lemma lem319571 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term165 A f P lt2 x g) = (term164 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319570 A P lt2 x f) (@lem319569 A P lt2 x g)). Qed.
Lemma lem319572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem319573 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term170 A f P lt2 x g) = (term171 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319572) (@lem319571 A f P lt2 x g)). Qed.
Lemma lem319574 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term167 A P lt2 x g z) = (term160 A P lt2 x g z).
Proof. exact (eq_refl (term167 A P lt2 x g z)). Qed.
Lemma lem319575 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term142 A P lt2 x f) = (term142 A P lt2 x f).
Proof. exact (eq_refl (term142 A P lt2 x f)). Qed.
Lemma lem319576 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term172 A f P lt2 x g z) = (term173 A f P lt2 x g z).
Proof. exact (MK_COMB (@lem319575 A P lt2 x f) (@lem319574 A P lt2 x g z)). Qed.
Lemma lem319577 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term174 A f P lt2 x g) = (term175 A f P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319576 A f P lt2 x g z)). Qed.
Lemma lem319578 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319579 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term166 A f P lt2 x g) = (term176 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319578 A) (@lem319577 A f P lt2 x g)). Qed.
Lemma lem319580 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term165 A f P lt2 x g) = (term166 A f P lt2 x g)) = ((term164 A f P lt2 x g) = (term176 A f P lt2 x g)).
Proof. exact (MK_COMB (@lem319573 A f P lt2 x g) (@lem319579 A f P lt2 x g)). Qed.
Lemma lem319581 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term164 A f P lt2 x g) = (term176 A f P lt2 x g).
Proof. exact (EQ_MP (@lem319580 A f P lt2 x g) (@lem319565 A f P lt2 x g)). Qed.
Lemma lem319582 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term144 A f P lt2 x g) = (term176 A f P lt2 x g).
Proof. exact (TRANS (@lem319561 A f P lt2 x g) (@lem319581 A f P lt2 x g)). Qed.
Lemma lem319583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem319584 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term146 A f P lt2 x g) = (term177 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319583) (@lem319582 A f P lt2 x g)). Qed.
Lemma lem319586 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem319587 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem319586 A P Q). Qed.
Lemma lem319588 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term151 A P lt2 x f) = (term152 A P lt2 x f).
Proof. exact (@lem319587 A (term153 A P x) (term128 A lt2 x f)). Qed.
Lemma lem319589 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term154 A lt2 x f z) = (term119 A lt2 x f z).
Proof. exact (eq_refl (term154 A lt2 x f z)). Qed.
Lemma lem319590 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term155 A lt2 x f) = (term128 A lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319589 A lt2 x f z)). Qed.
Lemma lem319591 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319592 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term156 A lt2 x f) = (term129 A lt2 x f).
Proof. exact (MK_COMB (@lem319591 A) (@lem319590 A lt2 x f)). Qed.
Lemma lem319593 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem319594 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term151 A P lt2 x f) = (term134 A P lt2 x f).
Proof. exact (MK_COMB (@lem319593 A P x) (@lem319592 A lt2 x f)). Qed.
Lemma lem319595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem319596 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term157 A P lt2 x f) = (term158 A P lt2 x f).
Proof. exact (MK_COMB (@lem319595) (@lem319594 A P lt2 x f)). Qed.
Lemma lem319597 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term154 A lt2 x f z) = (term119 A lt2 x f z).
Proof. exact (eq_refl (term154 A lt2 x f z)). Qed.
Lemma lem319598 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem319599 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term159 A P lt2 x f z) = (term160 A P lt2 x f z).
Proof. exact (MK_COMB (@lem319598 A P x) (@lem319597 A lt2 x f z)). Qed.
Lemma lem319600 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term161 A P lt2 x f) = (term162 A P lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319599 A P lt2 x f z)). Qed.
Lemma lem319601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319602 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term152 A P lt2 x f) = (term163 A P lt2 x f).
Proof. exact (MK_COMB (@lem319601 A) (@lem319600 A P lt2 x f)). Qed.
Lemma lem319603 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : ((term151 A P lt2 x f) = (term152 A P lt2 x f)) = ((term134 A P lt2 x f) = (term163 A P lt2 x f)).
Proof. exact (MK_COMB (@lem319596 A P lt2 x f) (@lem319602 A P lt2 x f)). Qed.
Lemma lem319604 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term134 A P lt2 x f) = (term163 A P lt2 x f).
Proof. exact (EQ_MP (@lem319603 A P lt2 x f) (@lem319588 A P lt2 x f)). Qed.
Lemma lem319605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem319606 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term138 A P lt2 x f) = (term178 A P lt2 x f).
Proof. exact (MK_COMB (@lem319605) (@lem319604 A P lt2 x f)). Qed.
Lemma lem319607 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term136 A P lt2 x g) = (term136 A P lt2 x g).
Proof. exact (eq_refl (term136 A P lt2 x g)). Qed.
Lemma lem319608 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term140 A f P lt2 x g) = (term179 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319606 A P lt2 x f) (@lem319607 A P lt2 x g)). Qed.
Lemma lem319610 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem319611 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (@lem319610 A P Q). Qed.
Lemma lem319612 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term182 A f P lt2 x g) = (term183 A f P lt2 x g).
Proof. exact (@lem319611 A (term162 A P lt2 x f) (term136 A P lt2 x g)). Qed.
Lemma lem319613 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term167 A P lt2 x f z) = (term160 A P lt2 x f z).
Proof. exact (eq_refl (term167 A P lt2 x f z)). Qed.
Lemma lem319614 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term168 A P lt2 x f) = (term162 A P lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319613 A P lt2 x f z)). Qed.
Lemma lem319615 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319616 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term169 A P lt2 x f) = (term163 A P lt2 x f).
Proof. exact (MK_COMB (@lem319615 A) (@lem319614 A P lt2 x f)). Qed.
Lemma lem319617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem319618 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term184 A P lt2 x f) = (term178 A P lt2 x f).
Proof. exact (MK_COMB (@lem319617) (@lem319616 A P lt2 x f)). Qed.
Lemma lem319619 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term136 A P lt2 x g) = (term136 A P lt2 x g).
Proof. exact (eq_refl (term136 A P lt2 x g)). Qed.
Lemma lem319620 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term182 A f P lt2 x g) = (term179 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319618 A P lt2 x f) (@lem319619 A P lt2 x g)). Qed.
Lemma lem319621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem319622 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term185 A f P lt2 x g) = (term186 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319621) (@lem319620 A f P lt2 x g)). Qed.
Lemma lem319623 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term167 A P lt2 x f z) = (term160 A P lt2 x f z).
Proof. exact (eq_refl (term167 A P lt2 x f z)). Qed.
Lemma lem319624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem319625 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term187 A P lt2 x f z) = (term188 A P lt2 x f z).
Proof. exact (MK_COMB (@lem319624) (@lem319623 A P lt2 x f z)). Qed.
Lemma lem319626 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term136 A P lt2 x g) = (term136 A P lt2 x g).
Proof. exact (eq_refl (term136 A P lt2 x g)). Qed.
Lemma lem319627 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term189 A f z P lt2 x g) = (term190 A f z P lt2 x g).
Proof. exact (MK_COMB (@lem319625 A P lt2 x f z) (@lem319626 A P lt2 x g)). Qed.
Lemma lem319628 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term191 A f P lt2 x g) = (term192 A f P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319627 A f z P lt2 x g)). Qed.
Lemma lem319629 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319630 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term183 A f P lt2 x g) = (term193 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319629 A) (@lem319628 A f P lt2 x g)). Qed.
Lemma lem319631 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term182 A f P lt2 x g) = (term183 A f P lt2 x g)) = ((term179 A f P lt2 x g) = (term193 A f P lt2 x g)).
Proof. exact (MK_COMB (@lem319622 A f P lt2 x g) (@lem319630 A f P lt2 x g)). Qed.
Lemma lem319632 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term179 A f P lt2 x g) = (term193 A f P lt2 x g).
Proof. exact (EQ_MP (@lem319631 A f P lt2 x g) (@lem319612 A f P lt2 x g)). Qed.
Lemma lem319633 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term140 A f P lt2 x g) = (term193 A f P lt2 x g).
Proof. exact (TRANS (@lem319608 A f P lt2 x g) (@lem319632 A f P lt2 x g)). Qed.
Lemma lem319634 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term148 A f P lt2 x g) = (term194 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319584 A f P lt2 x g) (@lem319633 A f P lt2 x g)). Qed.
Lemma lem319636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem319637 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (@lem319636 A P Q). Qed.
Lemma lem319638 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term197 A f P lt2 x g) = (term198 A f P lt2 x g).
Proof. exact (@lem319637 A (term175 A f P lt2 x g) (term192 A f P lt2 x g)). Qed.
Lemma lem319639 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term199 A f P lt2 x g z) = (term173 A f P lt2 x g z).
Proof. exact (eq_refl (term199 A f P lt2 x g z)). Qed.
Lemma lem319640 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term200 A f P lt2 x g) = (term175 A f P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319639 A f P lt2 x g z)). Qed.
Lemma lem319641 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319642 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term201 A f P lt2 x g) = (term176 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319641 A) (@lem319640 A f P lt2 x g)). Qed.
Lemma lem319643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem319644 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term202 A f P lt2 x g) = (term177 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319643) (@lem319642 A f P lt2 x g)). Qed.
Lemma lem319645 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term203 A f P lt2 x g z) = (term190 A f z P lt2 x g).
Proof. exact (eq_refl (term203 A f P lt2 x g z)). Qed.
Lemma lem319646 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term204 A f P lt2 x g) = (term192 A f P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319645 A f z P lt2 x g)). Qed.
Lemma lem319647 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319648 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term205 A f P lt2 x g) = (term193 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319647 A) (@lem319646 A f P lt2 x g)). Qed.
Lemma lem319649 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term197 A f P lt2 x g) = (term194 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319644 A f P lt2 x g) (@lem319648 A f P lt2 x g)). Qed.
Lemma lem319650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem319651 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term206 A f P lt2 x g) = (term207 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319650) (@lem319649 A f P lt2 x g)). Qed.
Lemma lem319652 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term199 A f P lt2 x g z) = (term173 A f P lt2 x g z).
Proof. exact (eq_refl (term199 A f P lt2 x g z)). Qed.
Lemma lem319653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem319654 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term208 A f P lt2 x g z) = (term209 A f P lt2 x g z).
Proof. exact (MK_COMB (@lem319653) (@lem319652 A f P lt2 x g z)). Qed.
Lemma lem319655 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term203 A f P lt2 x g z) = (term190 A f z P lt2 x g).
Proof. exact (eq_refl (term203 A f P lt2 x g z)). Qed.
Lemma lem319656 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term210 A f P lt2 x g z) = (term211 A f z P lt2 x g).
Proof. exact (MK_COMB (@lem319654 A f P lt2 x g z) (@lem319655 A f z P lt2 x g)). Qed.
Lemma lem319657 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term212 A f P lt2 x g) = (term213 A f P lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319656 A f z P lt2 x g)). Qed.
Lemma lem319658 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem319659 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term198 A f P lt2 x g) = (term214 A f P lt2 x g).
Proof. exact (MK_COMB (@lem319658 A) (@lem319657 A f P lt2 x g)). Qed.
Lemma lem319660 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : ((term197 A f P lt2 x g) = (term198 A f P lt2 x g)) = ((term194 A f P lt2 x g) = (term214 A f P lt2 x g)).
Proof. exact (MK_COMB (@lem319651 A f P lt2 x g) (@lem319659 A f P lt2 x g)). Qed.
Lemma lem319661 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term194 A f P lt2 x g) = (term214 A f P lt2 x g).
Proof. exact (EQ_MP (@lem319660 A f P lt2 x g) (@lem319638 A f P lt2 x g)). Qed.
Lemma lem319663 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term148 A f P lt2 x g) = (term214 A f P lt2 x g).
Proof. exact (TRANS (@lem319634 A f P lt2 x g) (@lem319661 A f P lt2 x g)). Qed.
Lemma lem319664 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term111 A f P lt2 x g) = (term214 A f P lt2 x g).
Proof. exact (TRANS (@lem319378 A f P lt2 x g) (@lem319663 A f P lt2 x g)). Qed.
Lemma lem319665 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term111 A f P lt2 x g) : term214 A f P lt2 x g.
Proof. exact (EQ_MP (@lem319664 A f P lt2 x g) (@lem319216 A f P lt2 x g h1)). Qed.
Lemma lem319666 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term211 A f z P lt2 x g) : term211 A f z P lt2 x g.
Proof. exact (h1). Qed.
Lemma lem319701 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term115 A lt2 x f g z) = (term115 A lt2 x f g z).
Proof. exact (eq_refl (term115 A lt2 x f g z)). Qed.
Lemma lem319702 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term116 A lt2 x f g) = (term116 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem319701 A lt2 x f g z)). Qed.
Lemma lem319703 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319704 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term117 A lt2 x f g) = (term117 A lt2 x f g).
Proof. exact (MK_COMB (@lem319703 A) (@lem319702 A lt2 x f g)). Qed.
Lemma lem319705 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term117 A lt2 x f g.
Proof. exact (EQ_MP (@lem319704 A lt2 x f g) (@lem319293 A lt2 x f g h1)). Qed.
Lemma lem319718 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term120 A lt2 x g z) = (term120 A lt2 x g z).
Proof. exact (eq_refl (term120 A lt2 x g z)). Qed.
Lemma lem319719 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term130 A lt2 x g) = (term130 A lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem319718 A lt2 x g z)). Qed.
Lemma lem319720 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319721 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term131 A lt2 x g) = (term131 A lt2 x g).
Proof. exact (MK_COMB (@lem319720 A) (@lem319719 A lt2 x g)). Qed.
Lemma lem319726 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem319727 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term136 A P lt2 x g) = (term136 A P lt2 x g).
Proof. exact (MK_COMB (@lem319726 A P x) (@lem319721 A lt2 x g)). Qed.
Lemma lem319750 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term188 A P lt2 x f z) = (term188 A P lt2 x f z).
Proof. exact (eq_refl (term188 A P lt2 x f z)). Qed.
Lemma lem319751 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term190 A f z P lt2 x g) = (term190 A f z P lt2 x g).
Proof. exact (MK_COMB (@lem319750 A P lt2 x f z) (@lem319727 A P lt2 x g)). Qed.
Lemma lem319772 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term160 A P lt2 x g z) = (term160 A P lt2 x g z).
Proof. exact (eq_refl (term160 A P lt2 x g z)). Qed.
Lemma lem319785 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term120 A lt2 x f z) = (term120 A lt2 x f z).
Proof. exact (eq_refl (term120 A lt2 x f z)). Qed.
Lemma lem319786 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term130 A lt2 x f) = (term130 A lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319785 A lt2 x f z)). Qed.
Lemma lem319787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319788 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term131 A lt2 x f) = (term131 A lt2 x f).
Proof. exact (MK_COMB (@lem319787 A) (@lem319786 A lt2 x f)). Qed.
Lemma lem319793 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem319794 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term136 A P lt2 x f) = (term136 A P lt2 x f).
Proof. exact (MK_COMB (@lem319793 A P x) (@lem319788 A lt2 x f)). Qed.
Lemma lem319795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem319796 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term142 A P lt2 x f) = (term142 A P lt2 x f).
Proof. exact (MK_COMB (@lem319795) (@lem319794 A P lt2 x f)). Qed.
Lemma lem319797 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term173 A f P lt2 x g z) = (term173 A f P lt2 x g z).
Proof. exact (MK_COMB (@lem319796 A P lt2 x f) (@lem319772 A P lt2 x g z)). Qed.
Lemma lem319798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem319799 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term209 A f P lt2 x g z) = (term209 A f P lt2 x g z).
Proof. exact (MK_COMB (@lem319798) (@lem319797 A f P lt2 x g z)). Qed.
Lemma lem319800 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term211 A f z P lt2 x g) = (term211 A f z P lt2 x g).
Proof. exact (MK_COMB (@lem319799 A f P lt2 x g z) (@lem319751 A f z P lt2 x g)). Qed.
Lemma lem319801 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term211 A f z P lt2 x g) : term211 A f z P lt2 x g.
Proof. exact (EQ_MP (@lem319800 A f z P lt2 x g) (@lem319666 A f z P lt2 x g h1)). Qed.
Lemma lem319802 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term173 A f P lt2 x g z.
Proof. exact (h1). Qed.
Lemma lem319803 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term190 A f z P lt2 x g.
Proof. exact (h1). Qed.
Lemma lem319804 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term160 A P lt2 x g z.
Proof. exact (proj2 (@lem319802 A f P lt2 x g z h1)). Qed.
Lemma lem319805 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term136 A P lt2 x f.
Proof. exact (proj1 (@lem319802 A f P lt2 x g z h1)). Qed.
Lemma lem319806 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term119 A lt2 x g z.
Proof. exact (proj2 (@lem319804 A f P lt2 x g z h1)). Qed.
Lemma lem319811 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term131 A lt2 x f.
Proof. exact (h1). Qed.
Lemma lem319812 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term136 A P lt2 x g.
Proof. exact (proj2 (@lem319803 A f z P lt2 x g h1)). Qed.
Lemma lem319813 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term160 A P lt2 x f z.
Proof. exact (proj1 (@lem319803 A f z P lt2 x g h1)). Qed.
Lemma lem319814 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term119 A lt2 x f z.
Proof. exact (proj2 (@lem319813 A f z P lt2 x g h1)). Qed.
Lemma lem319819 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term131 A lt2 x g.
Proof. exact (h1). Qed.
Lemma lem319870 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem319900 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term115 A lt2 x f g z) = (term215 A lt2 x f g z).
Proof. exact (@lem19490 (term216 A f g z) (term217 A lt2 z x) (term218 A f g z)). Qed.
Lemma lem319901 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term116 A lt2 x f g) = (term219 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem319900 A lt2 x f g z)). Qed.
Lemma lem319902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319904 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term117 A lt2 x f g) = (term220 A lt2 x f g).
Proof. exact (MK_COMB (@lem319902 A) (@lem319901 A lt2 x f g)). Qed.
Lemma lem319905 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term220 A lt2 x f g.
Proof. exact (EQ_MP (@lem319904 A lt2 x f g) (@lem319705 A lt2 x f g h1)). Qed.
Lemma lem319925 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (z : A) : (term120 A lt2 x f z) = (term120 A lt2 x f z).
Proof. exact (eq_refl (term120 A lt2 x f z)). Qed.
Lemma lem319926 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term130 A lt2 x f) = (term130 A lt2 x f).
Proof. exact (fun_ext (fun z : A => @lem319925 A lt2 x f z)). Qed.
Lemma lem319927 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem319929 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) : (term131 A lt2 x f) = (term131 A lt2 x f).
Proof. exact (MK_COMB (@lem319927 A) (@lem319926 A lt2 x f)). Qed.
Lemma lem319930 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term131 A lt2 x f.
Proof. exact (EQ_MP (@lem319929 A lt2 x f) (@lem319811 A lt2 x f h1)). Qed.
Lemma lem319981 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem320011 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (z : A) : (term115 A lt2 x f g z) = (term215 A lt2 x f g z).
Proof. exact (@lem19490 (term216 A f g z) (term217 A lt2 z x) (term218 A f g z)). Qed.
Lemma lem320012 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term116 A lt2 x f g) = (term219 A lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem320011 A lt2 x f g z)). Qed.
Lemma lem320013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320015 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) : (term117 A lt2 x f g) = (term220 A lt2 x f g).
Proof. exact (MK_COMB (@lem320013 A) (@lem320012 A lt2 x f g)). Qed.
Lemma lem320016 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term220 A lt2 x f g.
Proof. exact (EQ_MP (@lem320015 A lt2 x f g) (@lem319705 A lt2 x f g h1)). Qed.
Lemma lem320036 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) : (term120 A lt2 x g z) = (term120 A lt2 x g z).
Proof. exact (eq_refl (term120 A lt2 x g z)). Qed.
Lemma lem320037 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term130 A lt2 x g) = (term130 A lt2 x g).
Proof. exact (fun_ext (fun z : A => @lem320036 A lt2 x g z)). Qed.
Lemma lem320038 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320040 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) : (term131 A lt2 x g) = (term131 A lt2 x g).
Proof. exact (MK_COMB (@lem320038 A) (@lem320037 A lt2 x g)). Qed.
Lemma lem320041 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term131 A lt2 x g.
Proof. exact (EQ_MP (@lem320040 A lt2 x g) (@lem319819 A lt2 x g h1)). Qed.
Lemma lem320045 {A : Type'} (_7000 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term221 A lt2 x f g _7000.
Proof. exact (@lem319905 A lt2 x f g h1 _7000). Qed.
Lemma lem320046 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (_7000 : A) : (term221 A lt2 x f g _7000) = (term215 A lt2 x f g _7000).
Proof. exact (eq_refl (term221 A lt2 x f g _7000)). Qed.
Lemma lem320047 {A : Type'} (_7000 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term215 A lt2 x f g _7000.
Proof. exact (EQ_MP (@lem320046 A lt2 x f g _7000) (@lem320045 A _7000 lt2 x f g h1)). Qed.
Lemma lem320048 {A : Type'} (_7001 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term222 A lt2 x f _7001.
Proof. exact (@lem319930 A lt2 x f h1 _7001). Qed.
Lemma lem320049 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7001 : A) : (term222 A lt2 x f _7001) = (term120 A lt2 x f _7001).
Proof. exact (eq_refl (term222 A lt2 x f _7001)). Qed.
Lemma lem320054 {A : Type'} (_7003 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term221 A lt2 x f g _7003.
Proof. exact (@lem320016 A lt2 x f g h1 _7003). Qed.
Lemma lem320055 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (_7003 : A) : (term221 A lt2 x f g _7003) = (term215 A lt2 x f g _7003).
Proof. exact (eq_refl (term221 A lt2 x f g _7003)). Qed.
Lemma lem320056 {A : Type'} (_7003 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term215 A lt2 x f g _7003.
Proof. exact (EQ_MP (@lem320055 A lt2 x f g _7003) (@lem320054 A _7003 lt2 x f g h1)). Qed.
Lemma lem320057 {A : Type'} (_7004 : A) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term222 A lt2 x g _7004.
Proof. exact (@lem320041 A lt2 x g h1 _7004). Qed.
Lemma lem320058 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7004 : A) : (term222 A lt2 x g _7004) = (term120 A lt2 x g _7004).
Proof. exact (eq_refl (term222 A lt2 x g _7004)). Qed.
Lemma lem320069 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term153 A P x.
Proof. exact (proj1 (@lem319804 A f P lt2 x g z h1)). Qed.
Lemma lem320075 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem320101 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term153 A g z.
Proof. exact (proj2 (@lem319806 A f P lt2 x g z h1)). Qed.
Lemma lem320107 {A : Type'} (_7001 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term120 A lt2 x f _7001.
Proof. exact (EQ_MP (@lem320049 A lt2 x f _7001) (@lem320048 A _7001 lt2 x f h1)). Qed.
Lemma lem320127 {A : Type'} (_7000 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term223 A lt2 x f g _7000.
Proof. exact (proj2 (@lem320047 A _7000 lt2 x f g h1)). Qed.
Lemma lem320129 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term153 A P x.
Proof. exact (proj1 (@lem319813 A f z P lt2 x g h1)). Qed.
Lemma lem320135 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem320161 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term153 A f z.
Proof. exact (proj2 (@lem319814 A f z P lt2 x g h1)). Qed.
Lemma lem320167 {A : Type'} (_7004 : A) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term120 A lt2 x g _7004.
Proof. exact (EQ_MP (@lem320058 A lt2 x g _7004) (@lem320057 A _7004 lt2 x g h1)). Qed.
Lemma lem320177 {A : Type'} (_7003 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term224 A lt2 x f g _7003.
Proof. exact (proj1 (@lem320056 A _7003 lt2 x f g h1)). Qed.
Lemma lem320189 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem320190 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term225 A P x.
Proof. exact (fun h0 : term153 A P x => @lem320189 A P x h1). Qed.
Lemma lem320192 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320193 {A : Type'} (P : A -> Prop) (x : A) : (term225 A P x) = (P x).
Proof. exact (@lem320192 (P x)). Qed.
Lemma lem320194 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem320193 A P x) (@lem320190 A P x h1)). Qed.
Lemma lem320197 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem320199 {A : Type'} (P : A -> Prop) (x : A) : (term153 A P x) = (term227 A P x).
Proof. exact (@lem320197 (P x)). Qed.
Lemma lem320202 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term227 A P x.
Proof. exact (EQ_MP (@lem320199 A P x) (@lem320069 A f P lt2 x g z h1)). Qed.
Lemma lem320205 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : False.
Proof. exact (@lem320202 A f P lt2 x g z h2 (@lem320194 A P x h1)). Qed.
Lemma lem320206 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : term228.
Proof. exact (fun h0 : ~ False => @lem320205 A f P lt2 x g z h1 h2). Qed.
Lemma lem320208 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320209 : term228 = False.
Proof. exact (@lem320208 False). Qed.
Lemma lem320210 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : False.
Proof. exact (EQ_MP (@lem320209) (@lem320206 A f P lt2 x g z h1 h2)). Qed.
Lemma lem320212 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : lt2 z x.
Proof. exact (proj1 (@lem319806 A f P lt2 x g z h1)). Qed.
Lemma lem320213 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term229 A lt2 z x.
Proof. exact (fun h0 : term217 A lt2 z x => @lem320212 A f P lt2 x g z h1). Qed.
Lemma lem320215 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320216 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term229 A lt2 z x) = (lt2 z x).
Proof. exact (@lem320215 (lt2 z x)). Qed.
Lemma lem320217 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : lt2 z x.
Proof. exact (EQ_MP (@lem320216 A lt2 z x) (@lem320213 A f P lt2 x g z h1)). Qed.
Lemma lem320219 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : lt2 z x.
Proof. exact (proj1 (@lem319806 A f P lt2 x g z h1)). Qed.
Lemma lem320220 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term229 A lt2 z x.
Proof. exact (fun h0 : term217 A lt2 z x => @lem320219 A f P lt2 x g z h1). Qed.
Lemma lem320222 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320223 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term229 A lt2 z x) = (lt2 z x).
Proof. exact (@lem320222 (lt2 z x)). Qed.
Lemma lem320224 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : lt2 z x.
Proof. exact (EQ_MP (@lem320223 A lt2 z x) (@lem320220 A f P lt2 x g z h1)). Qed.
Lemma lem320230 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem320231 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : (term120 A lt2 x f _7001) = (term230 A f lt2 _7001 x).
Proof. exact (@lem320230 (f _7001) (term217 A lt2 _7001 x)). Qed.
Lemma lem320237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320238 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : (term231 A lt2 x f _7001) = (term232 A f lt2 _7001 x).
Proof. exact (MK_COMB (@lem320237) (@lem320231 A f lt2 _7001 x)). Qed.
Lemma lem320244 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : (term230 A f lt2 _7001 x) = (term230 A f lt2 _7001 x).
Proof. exact (eq_refl (term230 A f lt2 _7001 x)). Qed.
Lemma lem320245 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : ((term120 A lt2 x f _7001) = (term230 A f lt2 _7001 x)) = ((term230 A f lt2 _7001 x) = (term230 A f lt2 _7001 x)).
Proof. exact (MK_COMB (@lem320238 A f lt2 _7001 x) (@lem320244 A f lt2 _7001 x)). Qed.
Lemma lem320247 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem320248 (x : Prop) : (x = x) = True.
Proof. exact (@lem320247 Prop x). Qed.
Lemma lem320249 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : ((term230 A f lt2 _7001 x) = (term230 A f lt2 _7001 x)) = True.
Proof. exact (@lem320248 (term230 A f lt2 _7001 x)). Qed.
Lemma lem320250 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : ((term120 A lt2 x f _7001) = (term230 A f lt2 _7001 x)) = True.
Proof. exact (TRANS (@lem320245 A f lt2 _7001 x) (@lem320249 A f lt2 _7001 x)). Qed.
Lemma lem320251 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : True = ((term120 A lt2 x f _7001) = (term230 A f lt2 _7001 x)).
Proof. exact (SYM (@lem320250 A f lt2 _7001 x)). Qed.
Lemma lem320252 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (_7001 : A) (x : A) : (term120 A lt2 x f _7001) = (term230 A f lt2 _7001 x).
Proof. exact (EQ_MP (@lem320251 A f lt2 _7001 x) (@lem0)). Qed.
Lemma lem320253 {A : Type'} (_7001 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term230 A f lt2 _7001 x.
Proof. exact (EQ_MP (@lem320252 A f lt2 _7001 x) (@lem320107 A _7001 lt2 x f h1)). Qed.
Lemma lem320255 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem320256 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7001 : A) : (term230 A f lt2 _7001 x) = (term234 A lt2 x f _7001).
Proof. exact (@lem320255 (term217 A lt2 _7001 x) (f _7001)). Qed.
Lemma lem320258 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem320259 {A : Type'} (lt2 : type1402 A) (_7001 : A) (x : A) : (term235 A lt2 _7001 x) = (lt2 _7001 x).
Proof. exact (@lem320258 (lt2 _7001 x)). Qed.
Lemma lem320260 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320261 {A : Type'} (lt2 : type1402 A) (_7001 : A) (x : A) : (term236 A lt2 _7001 x) = (term237 A lt2 _7001 x).
Proof. exact (MK_COMB (@lem320260) (@lem320259 A lt2 _7001 x)). Qed.
Lemma lem320262 {A : Type'} (f : A -> Prop) (_7001 : A) : (f _7001) = (f _7001).
Proof. exact (eq_refl (f _7001)). Qed.
Lemma lem320263 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7001 : A) : (term234 A lt2 x f _7001) = (term103 A lt2 x f _7001).
Proof. exact (MK_COMB (@lem320261 A lt2 _7001 x) (@lem320262 A f _7001)). Qed.
Lemma lem320264 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7001 : A) : (term230 A f lt2 _7001 x) = (term103 A lt2 x f _7001).
Proof. exact (TRANS (@lem320256 A lt2 x f _7001) (@lem320263 A lt2 x f _7001)). Qed.
Lemma lem320267 {A : Type'} (_7001 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term103 A lt2 x f _7001.
Proof. exact (EQ_MP (@lem320264 A lt2 x f _7001) (@lem320253 A _7001 lt2 x f h1)). Qed.
Lemma lem320268 {A : Type'} (_7001 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term103 A lt2 x f _7001.
Proof. exact (@lem320267 A _7001 lt2 x f h1). Qed.
Lemma lem320269 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (h1 : term131 A lt2 x f) : term103 A lt2 x f z.
Proof. exact (@lem320268 A z lt2 x f h1). Qed.
Lemma lem320272 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term131 A lt2 x f) (h2 : term173 A f P lt2 x g z) : f z.
Proof. exact (@lem320269 A z lt2 x f h1 (@lem320224 A f P lt2 x g z h2)). Qed.
Lemma lem320273 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term131 A lt2 x f) (h2 : term173 A f P lt2 x g z) : term225 A f z.
Proof. exact (fun h0 : term153 A f z => @lem320272 A f P lt2 x g z h1 h2). Qed.
Lemma lem320275 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320276 {A : Type'} (f : A -> Prop) (z : A) : (term225 A f z) = (f z).
Proof. exact (@lem320275 (f z)). Qed.
Lemma lem320277 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term131 A lt2 x f) (h2 : term173 A f P lt2 x g z) : f z.
Proof. exact (EQ_MP (@lem320276 A f z) (@lem320273 A f P lt2 x g z h1 h2)). Qed.
Lemma lem320293 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem320294 {A : Type'} (g : A -> Prop) (f : A -> Prop) (_7000 : A) : (term218 A f g _7000) = (term216 A g f _7000).
Proof. exact (@lem320293 (g _7000) (term153 A f _7000)). Qed.
Lemma lem320300 {A : Type'} (lt2 : type1402 A) (_7000 : A) (x : A) : (term113 A lt2 _7000 x) = (term113 A lt2 _7000 x).
Proof. exact (eq_refl (term113 A lt2 _7000 x)). Qed.
Lemma lem320301 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (f : A -> Prop) (_7000 : A) : (term223 A lt2 x f g _7000) = (term224 A lt2 x g f _7000).
Proof. exact (MK_COMB (@lem320300 A lt2 _7000 x) (@lem320294 A g f _7000)). Qed.
Lemma lem320305 (q : Prop) (p : Prop) (r : Prop) : (term238 p q r) = (term238 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem320306 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term224 A lt2 x g f _7000) = (term239 A g lt2 x f _7000).
Proof. exact (@lem320305 (g _7000) (term217 A lt2 _7000 x) (term153 A f _7000)). Qed.
Lemma lem320322 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term223 A lt2 x f g _7000) = (term239 A g lt2 x f _7000).
Proof. exact (TRANS (@lem320301 A lt2 x g f _7000) (@lem320306 A g lt2 x f _7000)). Qed.
Lemma lem320323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320324 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term240 A lt2 x f g _7000) = (term241 A g lt2 x f _7000).
Proof. exact (MK_COMB (@lem320323) (@lem320322 A g lt2 x f _7000)). Qed.
Lemma lem320340 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term239 A g lt2 x f _7000) = (term239 A g lt2 x f _7000).
Proof. exact (eq_refl (term239 A g lt2 x f _7000)). Qed.
Lemma lem320341 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : ((term223 A lt2 x f g _7000) = (term239 A g lt2 x f _7000)) = ((term239 A g lt2 x f _7000) = (term239 A g lt2 x f _7000)).
Proof. exact (MK_COMB (@lem320324 A g lt2 x f _7000) (@lem320340 A g lt2 x f _7000)). Qed.
Lemma lem320343 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem320344 (x : Prop) : (x = x) = True.
Proof. exact (@lem320343 Prop x). Qed.
Lemma lem320345 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : ((term239 A g lt2 x f _7000) = (term239 A g lt2 x f _7000)) = True.
Proof. exact (@lem320344 (term239 A g lt2 x f _7000)). Qed.
Lemma lem320346 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : ((term223 A lt2 x f g _7000) = (term239 A g lt2 x f _7000)) = True.
Proof. exact (TRANS (@lem320341 A g lt2 x f _7000) (@lem320345 A g lt2 x f _7000)). Qed.
Lemma lem320347 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : True = ((term223 A lt2 x f g _7000) = (term239 A g lt2 x f _7000)).
Proof. exact (SYM (@lem320346 A g lt2 x f _7000)). Qed.
Lemma lem320348 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term223 A lt2 x f g _7000) = (term239 A g lt2 x f _7000).
Proof. exact (EQ_MP (@lem320347 A g lt2 x f _7000) (@lem0)). Qed.
Lemma lem320349 {A : Type'} (_7000 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term239 A g lt2 x f _7000.
Proof. exact (EQ_MP (@lem320348 A g lt2 x f _7000) (@lem320127 A _7000 lt2 x f g h1)). Qed.
Lemma lem320351 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem320352 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (_7000 : A) : (term239 A g lt2 x f _7000) = (term242 A lt2 x f g _7000).
Proof. exact (@lem320351 (term243 A lt2 x f _7000) (g _7000)). Qed.
Lemma lem320354 (a : Prop) (b : Prop) : (term244 a b) = (term245 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem320355 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term246 A lt2 x f _7000) = (term247 A lt2 x f _7000).
Proof. exact (@lem320354 (term217 A lt2 _7000 x) (term153 A f _7000)). Qed.
Lemma lem320357 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem320358 {A : Type'} (lt2 : type1402 A) (_7000 : A) (x : A) : (term235 A lt2 _7000 x) = (lt2 _7000 x).
Proof. exact (@lem320357 (lt2 _7000 x)). Qed.
Lemma lem320359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem320360 {A : Type'} (lt2 : type1402 A) (_7000 : A) (x : A) : (term248 A lt2 _7000 x) = (term249 A lt2 _7000 x).
Proof. exact (MK_COMB (@lem320359) (@lem320358 A lt2 _7000 x)). Qed.
Lemma lem320362 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem320363 {A : Type'} (f : A -> Prop) (_7000 : A) : (term250 A f _7000) = (f _7000).
Proof. exact (@lem320362 (f _7000)). Qed.
Lemma lem320364 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term247 A lt2 x f _7000) = (term251 A lt2 x f _7000).
Proof. exact (MK_COMB (@lem320360 A lt2 _7000 x) (@lem320363 A f _7000)). Qed.
Lemma lem320365 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term246 A lt2 x f _7000) = (term251 A lt2 x f _7000).
Proof. exact (TRANS (@lem320355 A lt2 x f _7000) (@lem320364 A lt2 x f _7000)). Qed.
Lemma lem320366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320367 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (_7000 : A) : (term252 A lt2 x f _7000) = (term253 A lt2 x f _7000).
Proof. exact (MK_COMB (@lem320366) (@lem320365 A lt2 x f _7000)). Qed.
Lemma lem320368 {A : Type'} (g : A -> Prop) (_7000 : A) : (g _7000) = (g _7000).
Proof. exact (eq_refl (g _7000)). Qed.
Lemma lem320369 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (_7000 : A) : (term242 A lt2 x f g _7000) = (term254 A lt2 x f g _7000).
Proof. exact (MK_COMB (@lem320367 A lt2 x f _7000) (@lem320368 A g _7000)). Qed.
Lemma lem320370 {A : Type'} (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (_7000 : A) : (term239 A g lt2 x f _7000) = (term254 A lt2 x f g _7000).
Proof. exact (TRANS (@lem320352 A lt2 x f g _7000) (@lem320369 A lt2 x f g _7000)). Qed.
Lemma lem320372 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term131 A lt2 x f) (h2 : term173 A f P lt2 x g z) : term251 A lt2 x f z.
Proof. exact (conj (@lem320217 A f P lt2 x g z h2) (@lem320277 A f P lt2 x g z h1 h2)). Qed.
Lemma lem320374 {A : Type'} (_7000 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term254 A lt2 x f g _7000.
Proof. exact (EQ_MP (@lem320370 A lt2 x f g _7000) (@lem320349 A _7000 lt2 x f g h1)). Qed.
Lemma lem320375 {A : Type'} (_7000 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term254 A lt2 x f g _7000.
Proof. exact (@lem320374 A _7000 lt2 x f g h1). Qed.
Lemma lem320376 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term254 A lt2 x f g z.
Proof. exact (@lem320375 A z lt2 x f g h1). Qed.
Lemma lem320379 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : g z.
Proof. exact (@lem320376 A z lt2 x f g h1 (@lem320372 A f P lt2 x g z h2 h3)). Qed.
Lemma lem320380 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : term225 A g z.
Proof. exact (fun h0 : term153 A g z => @lem320379 A f P lt2 x g z h1 h2 h3). Qed.
Lemma lem320382 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320383 {A : Type'} (g : A -> Prop) (z : A) : (term225 A g z) = (g z).
Proof. exact (@lem320382 (g z)). Qed.
Lemma lem320384 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : g z.
Proof. exact (EQ_MP (@lem320383 A g z) (@lem320380 A f P lt2 x g z h1 h2 h3)). Qed.
Lemma lem320387 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem320389 {A : Type'} (g : A -> Prop) (z : A) : (term153 A g z) = (term227 A g z).
Proof. exact (@lem320387 (g z)). Qed.
Lemma lem320392 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term173 A f P lt2 x g z) : term227 A g z.
Proof. exact (EQ_MP (@lem320389 A g z) (@lem320101 A f P lt2 x g z h1)). Qed.
Lemma lem320395 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : False.
Proof. exact (@lem320392 A f P lt2 x g z h3 (@lem320384 A f P lt2 x g z h1 h2 h3)). Qed.
Lemma lem320396 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : term228.
Proof. exact (fun h0 : ~ False => @lem320395 A f P lt2 x g z h1 h2 h3). Qed.
Lemma lem320398 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320399 : term228 = False.
Proof. exact (@lem320398 False). Qed.
Lemma lem320400 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : False.
Proof. exact (EQ_MP (@lem320399) (@lem320396 A f P lt2 x g z h1 h2 h3)). Qed.
Lemma lem320402 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem320403 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term225 A P x.
Proof. exact (fun h0 : term153 A P x => @lem320402 A P x h1). Qed.
Lemma lem320405 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320406 {A : Type'} (P : A -> Prop) (x : A) : (term225 A P x) = (P x).
Proof. exact (@lem320405 (P x)). Qed.
Lemma lem320407 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem320406 A P x) (@lem320403 A P x h1)). Qed.
Lemma lem320410 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem320412 {A : Type'} (P : A -> Prop) (x : A) : (term153 A P x) = (term227 A P x).
Proof. exact (@lem320410 (P x)). Qed.
Lemma lem320415 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term227 A P x.
Proof. exact (EQ_MP (@lem320412 A P x) (@lem320129 A f z P lt2 x g h1)). Qed.
Lemma lem320418 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : False.
Proof. exact (@lem320415 A f z P lt2 x g h2 (@lem320407 A P x h1)). Qed.
Lemma lem320419 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : term228.
Proof. exact (fun h0 : ~ False => @lem320418 A f z P lt2 x g h1 h2). Qed.
Lemma lem320421 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320422 : term228 = False.
Proof. exact (@lem320421 False). Qed.
Lemma lem320423 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320422) (@lem320419 A f z P lt2 x g h1 h2)). Qed.
Lemma lem320425 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : lt2 z x.
Proof. exact (proj1 (@lem319814 A f z P lt2 x g h1)). Qed.
Lemma lem320426 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term229 A lt2 z x.
Proof. exact (fun h0 : term217 A lt2 z x => @lem320425 A f z P lt2 x g h1). Qed.
Lemma lem320428 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320429 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term229 A lt2 z x) = (lt2 z x).
Proof. exact (@lem320428 (lt2 z x)). Qed.
Lemma lem320430 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : lt2 z x.
Proof. exact (EQ_MP (@lem320429 A lt2 z x) (@lem320426 A f z P lt2 x g h1)). Qed.
Lemma lem320432 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : lt2 z x.
Proof. exact (proj1 (@lem319814 A f z P lt2 x g h1)). Qed.
Lemma lem320433 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term229 A lt2 z x.
Proof. exact (fun h0 : term217 A lt2 z x => @lem320432 A f z P lt2 x g h1). Qed.
Lemma lem320435 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320436 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term229 A lt2 z x) = (lt2 z x).
Proof. exact (@lem320435 (lt2 z x)). Qed.
Lemma lem320437 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : lt2 z x.
Proof. exact (EQ_MP (@lem320436 A lt2 z x) (@lem320433 A f z P lt2 x g h1)). Qed.
Lemma lem320443 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem320444 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : (term120 A lt2 x g _7004) = (term230 A g lt2 _7004 x).
Proof. exact (@lem320443 (g _7004) (term217 A lt2 _7004 x)). Qed.
Lemma lem320450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320451 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : (term231 A lt2 x g _7004) = (term232 A g lt2 _7004 x).
Proof. exact (MK_COMB (@lem320450) (@lem320444 A g lt2 _7004 x)). Qed.
Lemma lem320457 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : (term230 A g lt2 _7004 x) = (term230 A g lt2 _7004 x).
Proof. exact (eq_refl (term230 A g lt2 _7004 x)). Qed.
Lemma lem320458 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : ((term120 A lt2 x g _7004) = (term230 A g lt2 _7004 x)) = ((term230 A g lt2 _7004 x) = (term230 A g lt2 _7004 x)).
Proof. exact (MK_COMB (@lem320451 A g lt2 _7004 x) (@lem320457 A g lt2 _7004 x)). Qed.
Lemma lem320460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem320461 (x : Prop) : (x = x) = True.
Proof. exact (@lem320460 Prop x). Qed.
Lemma lem320462 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : ((term230 A g lt2 _7004 x) = (term230 A g lt2 _7004 x)) = True.
Proof. exact (@lem320461 (term230 A g lt2 _7004 x)). Qed.
Lemma lem320463 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : ((term120 A lt2 x g _7004) = (term230 A g lt2 _7004 x)) = True.
Proof. exact (TRANS (@lem320458 A g lt2 _7004 x) (@lem320462 A g lt2 _7004 x)). Qed.
Lemma lem320464 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : True = ((term120 A lt2 x g _7004) = (term230 A g lt2 _7004 x)).
Proof. exact (SYM (@lem320463 A g lt2 _7004 x)). Qed.
Lemma lem320465 {A : Type'} (g : A -> Prop) (lt2 : type1402 A) (_7004 : A) (x : A) : (term120 A lt2 x g _7004) = (term230 A g lt2 _7004 x).
Proof. exact (EQ_MP (@lem320464 A g lt2 _7004 x) (@lem0)). Qed.
Lemma lem320466 {A : Type'} (_7004 : A) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term230 A g lt2 _7004 x.
Proof. exact (EQ_MP (@lem320465 A g lt2 _7004 x) (@lem320167 A _7004 lt2 x g h1)). Qed.
Lemma lem320468 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem320469 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7004 : A) : (term230 A g lt2 _7004 x) = (term234 A lt2 x g _7004).
Proof. exact (@lem320468 (term217 A lt2 _7004 x) (g _7004)). Qed.
Lemma lem320471 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem320472 {A : Type'} (lt2 : type1402 A) (_7004 : A) (x : A) : (term235 A lt2 _7004 x) = (lt2 _7004 x).
Proof. exact (@lem320471 (lt2 _7004 x)). Qed.
Lemma lem320473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320474 {A : Type'} (lt2 : type1402 A) (_7004 : A) (x : A) : (term236 A lt2 _7004 x) = (term237 A lt2 _7004 x).
Proof. exact (MK_COMB (@lem320473) (@lem320472 A lt2 _7004 x)). Qed.
Lemma lem320475 {A : Type'} (g : A -> Prop) (_7004 : A) : (g _7004) = (g _7004).
Proof. exact (eq_refl (g _7004)). Qed.
Lemma lem320476 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7004 : A) : (term234 A lt2 x g _7004) = (term103 A lt2 x g _7004).
Proof. exact (MK_COMB (@lem320474 A lt2 _7004 x) (@lem320475 A g _7004)). Qed.
Lemma lem320477 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7004 : A) : (term230 A g lt2 _7004 x) = (term103 A lt2 x g _7004).
Proof. exact (TRANS (@lem320469 A lt2 x g _7004) (@lem320476 A lt2 x g _7004)). Qed.
Lemma lem320480 {A : Type'} (_7004 : A) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term103 A lt2 x g _7004.
Proof. exact (EQ_MP (@lem320477 A lt2 x g _7004) (@lem320466 A _7004 lt2 x g h1)). Qed.
Lemma lem320481 {A : Type'} (_7004 : A) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term103 A lt2 x g _7004.
Proof. exact (@lem320480 A _7004 lt2 x g h1). Qed.
Lemma lem320482 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) : term103 A lt2 x g z.
Proof. exact (@lem320481 A z lt2 x g h1). Qed.
Lemma lem320485 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) (h2 : term190 A f z P lt2 x g) : g z.
Proof. exact (@lem320482 A z lt2 x g h1 (@lem320437 A f z P lt2 x g h2)). Qed.
Lemma lem320486 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) (h2 : term190 A f z P lt2 x g) : term225 A g z.
Proof. exact (fun h0 : term153 A g z => @lem320485 A f z P lt2 x g h1 h2). Qed.
Lemma lem320488 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320489 {A : Type'} (g : A -> Prop) (z : A) : (term225 A g z) = (g z).
Proof. exact (@lem320488 (g z)). Qed.
Lemma lem320490 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) (h2 : term190 A f z P lt2 x g) : g z.
Proof. exact (EQ_MP (@lem320489 A g z) (@lem320486 A f z P lt2 x g h1 h2)). Qed.
Lemma lem320496 (q : Prop) (p : Prop) (r : Prop) : (term238 p q r) = (term238 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem320497 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term224 A lt2 x f g _7003) = (term239 A f lt2 x g _7003).
Proof. exact (@lem320496 (f _7003) (term217 A lt2 _7003 x) (term153 A g _7003)). Qed.
Lemma lem320513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320514 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term255 A lt2 x f g _7003) = (term241 A f lt2 x g _7003).
Proof. exact (MK_COMB (@lem320513) (@lem320497 A f lt2 x g _7003)). Qed.
Lemma lem320530 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term239 A f lt2 x g _7003) = (term239 A f lt2 x g _7003).
Proof. exact (eq_refl (term239 A f lt2 x g _7003)). Qed.
Lemma lem320531 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : ((term224 A lt2 x f g _7003) = (term239 A f lt2 x g _7003)) = ((term239 A f lt2 x g _7003) = (term239 A f lt2 x g _7003)).
Proof. exact (MK_COMB (@lem320514 A f lt2 x g _7003) (@lem320530 A f lt2 x g _7003)). Qed.
Lemma lem320533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem320534 (x : Prop) : (x = x) = True.
Proof. exact (@lem320533 Prop x). Qed.
Lemma lem320535 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : ((term239 A f lt2 x g _7003) = (term239 A f lt2 x g _7003)) = True.
Proof. exact (@lem320534 (term239 A f lt2 x g _7003)). Qed.
Lemma lem320536 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : ((term224 A lt2 x f g _7003) = (term239 A f lt2 x g _7003)) = True.
Proof. exact (TRANS (@lem320531 A f lt2 x g _7003) (@lem320535 A f lt2 x g _7003)). Qed.
Lemma lem320537 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : True = ((term224 A lt2 x f g _7003) = (term239 A f lt2 x g _7003)).
Proof. exact (SYM (@lem320536 A f lt2 x g _7003)). Qed.
Lemma lem320538 {A : Type'} (f : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term224 A lt2 x f g _7003) = (term239 A f lt2 x g _7003).
Proof. exact (EQ_MP (@lem320537 A f lt2 x g _7003) (@lem0)). Qed.
Lemma lem320539 {A : Type'} (_7003 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term239 A f lt2 x g _7003.
Proof. exact (EQ_MP (@lem320538 A f lt2 x g _7003) (@lem320177 A _7003 lt2 x f g h1)). Qed.
Lemma lem320541 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem320542 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (f : A -> Prop) (_7003 : A) : (term239 A f lt2 x g _7003) = (term242 A lt2 x g f _7003).
Proof. exact (@lem320541 (term243 A lt2 x g _7003) (f _7003)). Qed.
Lemma lem320544 (a : Prop) (b : Prop) : (term244 a b) = (term245 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem320545 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term246 A lt2 x g _7003) = (term247 A lt2 x g _7003).
Proof. exact (@lem320544 (term217 A lt2 _7003 x) (term153 A g _7003)). Qed.
Lemma lem320547 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem320548 {A : Type'} (lt2 : type1402 A) (_7003 : A) (x : A) : (term235 A lt2 _7003 x) = (lt2 _7003 x).
Proof. exact (@lem320547 (lt2 _7003 x)). Qed.
Lemma lem320549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem320550 {A : Type'} (lt2 : type1402 A) (_7003 : A) (x : A) : (term248 A lt2 _7003 x) = (term249 A lt2 _7003 x).
Proof. exact (MK_COMB (@lem320549) (@lem320548 A lt2 _7003 x)). Qed.
Lemma lem320552 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem320553 {A : Type'} (g : A -> Prop) (_7003 : A) : (term250 A g _7003) = (g _7003).
Proof. exact (@lem320552 (g _7003)). Qed.
Lemma lem320554 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term247 A lt2 x g _7003) = (term251 A lt2 x g _7003).
Proof. exact (MK_COMB (@lem320550 A lt2 _7003 x) (@lem320553 A g _7003)). Qed.
Lemma lem320555 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term246 A lt2 x g _7003) = (term251 A lt2 x g _7003).
Proof. exact (TRANS (@lem320545 A lt2 x g _7003) (@lem320554 A lt2 x g _7003)). Qed.
Lemma lem320556 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320557 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (_7003 : A) : (term252 A lt2 x g _7003) = (term253 A lt2 x g _7003).
Proof. exact (MK_COMB (@lem320556) (@lem320555 A lt2 x g _7003)). Qed.
Lemma lem320558 {A : Type'} (f : A -> Prop) (_7003 : A) : (f _7003) = (f _7003).
Proof. exact (eq_refl (f _7003)). Qed.
Lemma lem320559 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (f : A -> Prop) (_7003 : A) : (term242 A lt2 x g f _7003) = (term254 A lt2 x g f _7003).
Proof. exact (MK_COMB (@lem320557 A lt2 x g _7003) (@lem320558 A f _7003)). Qed.
Lemma lem320560 {A : Type'} (lt2 : type1402 A) (x : A) (g : A -> Prop) (f : A -> Prop) (_7003 : A) : (term239 A f lt2 x g _7003) = (term254 A lt2 x g f _7003).
Proof. exact (TRANS (@lem320542 A lt2 x g f _7003) (@lem320559 A lt2 x g f _7003)). Qed.
Lemma lem320562 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term131 A lt2 x g) (h2 : term190 A f z P lt2 x g) : term251 A lt2 x g z.
Proof. exact (conj (@lem320430 A f z P lt2 x g h2) (@lem320490 A f z P lt2 x g h1 h2)). Qed.
Lemma lem320564 {A : Type'} (_7003 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term254 A lt2 x g f _7003.
Proof. exact (EQ_MP (@lem320560 A lt2 x g f _7003) (@lem320539 A _7003 lt2 x f g h1)). Qed.
Lemma lem320565 {A : Type'} (_7003 : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term254 A lt2 x g f _7003.
Proof. exact (@lem320564 A _7003 lt2 x f g h1). Qed.
Lemma lem320566 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term254 A lt2 x g f z.
Proof. exact (@lem320565 A z lt2 x f g h1). Qed.
Lemma lem320569 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : f z.
Proof. exact (@lem320566 A z lt2 x f g h1 (@lem320562 A f z P lt2 x g h2 h3)). Qed.
Lemma lem320570 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : term225 A f z.
Proof. exact (fun h0 : term153 A f z => @lem320569 A f z P lt2 x g h1 h2 h3). Qed.
Lemma lem320572 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320573 {A : Type'} (f : A -> Prop) (z : A) : (term225 A f z) = (f z).
Proof. exact (@lem320572 (f z)). Qed.
Lemma lem320574 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : f z.
Proof. exact (EQ_MP (@lem320573 A f z) (@lem320570 A f z P lt2 x g h1 h2 h3)). Qed.
Lemma lem320577 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem320579 {A : Type'} (f : A -> Prop) (z : A) : (term153 A f z) = (term227 A f z).
Proof. exact (@lem320577 (f z)). Qed.
Lemma lem320582 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term190 A f z P lt2 x g) : term227 A f z.
Proof. exact (EQ_MP (@lem320579 A f z) (@lem320161 A f z P lt2 x g h1)). Qed.
Lemma lem320585 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : False.
Proof. exact (@lem320582 A f z P lt2 x g h3 (@lem320574 A f z P lt2 x g h1 h2 h3)). Qed.
Lemma lem320586 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : term228.
Proof. exact (fun h0 : ~ False => @lem320585 A f z P lt2 x g h1 h2 h3). Qed.
Lemma lem320588 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem320589 : term228 = False.
Proof. exact (@lem320588 False). Qed.
Lemma lem320590 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320589) (@lem320586 A f z P lt2 x g h1 h2 h3)). Qed.
Lemma lem320591 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem320423 A f z P lt2 x g h1 h2) (fun h3 : False => @lem320135 A P x h1)). Qed.
Lemma lem320592 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320591 A f z P lt2 x g h1 h2) (@lem320135 A P x h1)). Qed.
Lemma lem320593 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem320210 A f P lt2 x g z h1 h2) (fun h3 : False => @lem320075 A P x h1)). Qed.
Lemma lem320594 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : False.
Proof. exact (EQ_MP (@lem320593 A f P lt2 x g z h1 h2) (@lem320075 A P x h1)). Qed.
Lemma lem320595 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem320592 A f z P lt2 x g h1 h2) (fun h3 : False => @lem319981 A P x h1)). Qed.
Lemma lem320596 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320595 A f z P lt2 x g h1 h2) (@lem319981 A P x h1)). Qed.
Lemma lem320597 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem320594 A f P lt2 x g z h1 h2) (fun h3 : False => @lem319870 A P x h1)). Qed.
Lemma lem320598 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : False.
Proof. exact (EQ_MP (@lem320597 A f P lt2 x g z h1 h2) (@lem319870 A P x h1)). Qed.
Lemma lem320599 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : (term131 A lt2 x g) = False.
Proof. exact (prop_ext (fun h4 : term131 A lt2 x g => @lem320590 A f z P lt2 x g h1 h2 h3) (fun h4 : False => @lem320041 A lt2 x g h2)). Qed.
Lemma lem320600 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x g) (h3 : term190 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320599 A f z P lt2 x g h1 h2 h3) (@lem320041 A lt2 x g h2)). Qed.
Lemma lem320601 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem320596 A f z P lt2 x g h1 h2) (fun h3 : False => @lem319981 A P x h1)). Qed.
Lemma lem320602 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : P x) (h2 : term190 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320601 A f z P lt2 x g h1 h2) (@lem319981 A P x h1)). Qed.
Lemma lem320603 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : (term131 A lt2 x f) = False.
Proof. exact (prop_ext (fun h4 : term131 A lt2 x f => @lem320400 A f P lt2 x g z h1 h2 h3) (fun h4 : False => @lem319930 A lt2 x f h2)). Qed.
Lemma lem320604 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term131 A lt2 x f) (h3 : term173 A f P lt2 x g z) : False.
Proof. exact (EQ_MP (@lem320603 A f P lt2 x g z h1 h2 h3) (@lem319930 A lt2 x f h2)). Qed.
Lemma lem320605 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem320598 A f P lt2 x g z h1 h2) (fun h3 : False => @lem319870 A P x h1)). Qed.
Lemma lem320606 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : P x) (h2 : term173 A f P lt2 x g z) : False.
Proof. exact (EQ_MP (@lem320605 A f P lt2 x g z h1 h2) (@lem319870 A P x h1)). Qed.
Lemma lem320607 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term190 A f z P lt2 x g) : False.
Proof. exact (or_elim (@lem319812 A f z P lt2 x g h2) (fun h0 : P x => @lem320602 A f z P lt2 x g h0 h2) (fun h0 : term131 A lt2 x g => @lem320600 A f z P lt2 x g h1 h0 h2)). Qed.
Lemma lem320608 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (z : A) (h1 : term109 A lt2 x f g) (h2 : term173 A f P lt2 x g z) : False.
Proof. exact (or_elim (@lem319805 A f P lt2 x g z h2) (fun h0 : P x => @lem320606 A f P lt2 x g z h0 h2) (fun h0 : term131 A lt2 x f => @lem320604 A f P lt2 x g z h1 h0 h2)). Qed.
Lemma lem320609 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term211 A f z P lt2 x g) : False.
Proof. exact (or_elim (@lem319801 A f z P lt2 x g h2) (fun h0 : term173 A f P lt2 x g z => @lem320608 A f P lt2 x g z h1 h0) (fun h0 : term190 A f z P lt2 x g => @lem320607 A f z P lt2 x g h1 h0)). Qed.
Lemma lem320610 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term211 A f z P lt2 x g) : (term211 A f z P lt2 x g) = False.
Proof. exact (prop_ext (fun h3 : term211 A f z P lt2 x g => @lem320609 A f z P lt2 x g h1 h2) (fun h3 : False => @lem319801 A f z P lt2 x g h2)). Qed.
Lemma lem320611 {A : Type'} (f : A -> Prop) (z : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term211 A f z P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320610 A f z P lt2 x g h1 h2) (@lem319801 A f z P lt2 x g h2)). Qed.
Lemma lem320612 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term111 A f P lt2 x g) : False.
Proof. exact (ex_elim (@lem319665 A f P lt2 x g h2) (fun z : A => fun h0 : term213 A f P lt2 x g z => @lem320611 A f z P lt2 x g h1 h0)). Qed.
Lemma lem320613 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term111 A f P lt2 x g) : (term111 A f P lt2 x g) = False.
Proof. exact (prop_ext (fun h3 : term111 A f P lt2 x g => @lem320612 A f P lt2 x g h1 h2) (fun h3 : False => @lem319216 A f P lt2 x g h2)). Qed.
Lemma lem320614 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) (h1 : term109 A lt2 x f g) (h2 : term111 A f P lt2 x g) : False.
Proof. exact (EQ_MP (@lem320613 A f P lt2 x g h1 h2) (@lem319216 A f P lt2 x g h2)). Qed.
Lemma lem320615 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : term110 A f P lt2 x g.
Proof. exact (fun h0 : term111 A f P lt2 x g => @lem320614 A f P lt2 x g h1 h0). Qed.
Lemma lem320616 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (f : A -> Prop) (g : A -> Prop) (h1 : term109 A lt2 x f g) : (term25 A P lt2 x f) = (term25 A P lt2 x g).
Proof. exact (EQ_MP (@lem319215 A f P lt2 x g) (@lem320615 A P lt2 x f g h1)). Qed.
Lemma lem320617 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (x : A) (g : A -> Prop) : term33 A f P lt2 x g.
Proof. exact (fun h0 : term109 A lt2 x f g => @lem320616 A P lt2 x f g h0). Qed.
Lemma lem320622 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) (g : A -> Prop) : term37 A f P lt2 g.
Proof. exact (fun x : A => @lem320617 A f P lt2 x g). Qed.
Lemma lem320627 {A : Type'} (f : A -> Prop) (P : A -> Prop) (lt2 : type1402 A) : term41 A f P lt2.
Proof. exact (fun g : A -> Prop => @lem320622 A f P lt2 g). Qed.
Lemma lem320632 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term45 A P lt2.
Proof. exact (fun f : A -> Prop => @lem320627 A f P lt2). Qed.
Lemma lem320637 {A : Type'} (lt2 : type1402 A) : term98 A lt2.
Proof. exact (fun P : A -> Prop => @lem320632 A P lt2). Qed.
Lemma lem320642 {A : Type'} : term102 A.
Proof. exact (fun lt2 : type1402 A => @lem320637 A lt2). Qed.
Lemma lem320643 {A : Type'} : term101 A.
Proof. exact (EQ_MP (@lem319210 A) (@lem320642 A)). Qed.
Lemma lem320644 {A : Type'} (lt2 : type1402 A) : term256 A lt2.
Proof. exact (@lem320643 A lt2). Qed.
Lemma lem320645 {A : Type'} (lt2 : type1402 A) : (term256 A lt2) = (term97 A lt2).
Proof. exact (eq_refl (term256 A lt2)). Qed.
Lemma lem320646 {A : Type'} (lt2 : type1402 A) : term97 A lt2.
Proof. exact (EQ_MP (@lem320645 A lt2) (@lem320644 A lt2)). Qed.
Lemma lem320647 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term257 A lt2 P.
Proof. exact (@lem320646 A lt2 P). Qed.
Lemma lem320648 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term257 A lt2 P) = (term88 A P lt2).
Proof. exact (eq_refl (term257 A lt2 P)). Qed.
Lemma lem320649 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term88 A P lt2.
Proof. exact (EQ_MP (@lem320648 A P lt2) (@lem320647 A lt2 P)). Qed.
Lemma lem320651 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term88 A P lt2.
Proof. exact (@lem319020 A P lt2 (@lem320649 A P lt2)). Qed.
Lemma lem320652 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term89 A P lt2) : False.
Proof. exact (@lem320651 A P lt2 (@lem319004 A P lt2 h1)). Qed.
Lemma lem320653 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term89 A P lt2) : (term89 A P lt2) = False.
Proof. exact (prop_ext (fun h2 : term89 A P lt2 => @lem320652 A P lt2 h1) (fun h2 : False => @lem319004 A P lt2 h1)). Qed.
Lemma lem320654 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term89 A P lt2) : False.
Proof. exact (EQ_MP (@lem320653 A P lt2 h1) (@lem319004 A P lt2 h1)). Qed.
Lemma lem320655 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term88 A P lt2.
Proof. exact (fun h0 : term89 A P lt2 => @lem320654 A P lt2 h0). Qed.
Lemma lem320656 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term45 A P lt2.
Proof. exact (EQ_MP (@lem319003 A P lt2) (@lem320655 A P lt2)). Qed.
Lemma lem320657 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term68 A P lt2) : term68 A P lt2.
Proof. exact (h1). Qed.
Lemma lem320658 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term68 A P lt2) : term258 A lt2 P.
Proof. exact (@lem320657 A P lt2 h1 P). Qed.
Lemma lem320659 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term258 A lt2 P) = (term259 A lt2 P).
Proof. exact (eq_refl (term258 A lt2 P)). Qed.
Lemma lem320660 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term68 A P lt2) : term259 A lt2 P.
Proof. exact (EQ_MP (@lem320659 A lt2 P) (@lem320658 A P lt2 h1)). Qed.
Lemma lem320661 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term68 A P lt2) : term260 A lt2 P.
Proof. exact (@lem320660 A P lt2 h1 (term78 A)). Qed.
Lemma lem320662 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term260 A lt2 P) = (term261 A lt2 P).
Proof. exact (eq_refl (term260 A lt2 P)). Qed.
Lemma lem320663 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term68 A P lt2) : term261 A lt2 P.
Proof. exact (EQ_MP (@lem320662 A lt2 P) (@lem320661 A P lt2 h1)). Qed.
Lemma lem320695 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem320696 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem320695 A Prop f y). Qed.
Lemma lem320697 {A : Type'} (x : A) : (term262 A x) = (term263 A x).
Proof. exact (@lem320696 A (term78 A) x). Qed.
Lemma lem320698 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (eq_refl (term263 A x)). Qed.
Lemma lem320699 {A : Type'} : (term264 A) = (term78 A).
Proof. exact (fun_ext (fun x : A => @lem320698 A x)). Qed.
Lemma lem320700 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem320701 {A : Type'} (x : A) : (term262 A x) = (term263 A x).
Proof. exact (MK_COMB (@lem320699 A) (@lem320700 A x)). Qed.
Lemma lem320702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320703 {A : Type'} (x : A) : (term265 A x) = (term266 A x).
Proof. exact (MK_COMB (@lem320702) (@lem320701 A x)). Qed.
Lemma lem320704 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (eq_refl (term263 A x)). Qed.
Lemma lem320705 {A : Type'} (x : A) : ((term262 A x) = (term263 A x)) = ((term263 A x) = True).
Proof. exact (MK_COMB (@lem320703 A x) (@lem320704 A x)). Qed.
Lemma lem320706 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (EQ_MP (@lem320705 A x) (@lem320697 A x)). Qed.
Lemma lem320707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320708 {A : Type'} (x : A) : (term266 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem320707) (@lem320706 A x)). Qed.
Lemma lem320718 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem320719 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem320718 A Prop f y). Qed.
Lemma lem320720 {A : Type'} (z : A) : (term262 A z) = (term263 A z).
Proof. exact (@lem320719 A (term78 A) z). Qed.
Lemma lem320721 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (eq_refl (term263 A x)). Qed.
Lemma lem320722 {A : Type'} : (term264 A) = (term78 A).
Proof. exact (fun_ext (fun x : A => @lem320721 A x)). Qed.
Lemma lem320723 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem320724 {A : Type'} (z : A) : (term262 A z) = (term263 A z).
Proof. exact (MK_COMB (@lem320722 A) (@lem320723 A z)). Qed.
Lemma lem320725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320726 {A : Type'} (z : A) : (term265 A z) = (term266 A z).
Proof. exact (MK_COMB (@lem320725) (@lem320724 A z)). Qed.
Lemma lem320727 {A : Type'} (z : A) : (term263 A z) = True.
Proof. exact (eq_refl (term263 A z)). Qed.
Lemma lem320728 {A : Type'} (z : A) : ((term262 A z) = (term263 A z)) = ((term263 A z) = True).
Proof. exact (MK_COMB (@lem320726 A z) (@lem320727 A z)). Qed.
Lemma lem320729 {A : Type'} (z : A) : (term263 A z) = True.
Proof. exact (EQ_MP (@lem320728 A z) (@lem320720 A z)). Qed.
Lemma lem320730 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term237 A lt2 z x) = (term237 A lt2 z x).
Proof. exact (eq_refl (term237 A lt2 z x)). Qed.
Lemma lem320731 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term267 A lt2 x z) = (term268 A lt2 z x).
Proof. exact (MK_COMB (@lem320730 A lt2 z x) (@lem320729 A z)). Qed.
Lemma lem320733 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem320734 {A : Type'} (lt2 : type1402 A) (z : A) (x : A) : (term268 A lt2 z x) = True.
Proof. exact (@lem320733 (lt2 z x)). Qed.
Lemma lem320735 {A : Type'} (lt2 : type1402 A) (x : A) (z : A) : (term267 A lt2 x z) = True.
Proof. exact (TRANS (@lem320731 A lt2 z x) (@lem320734 A lt2 z x)). Qed.
Lemma lem320736 {A : Type'} (lt2 : type1402 A) (x : A) : (term269 A lt2 x) = (term78 A).
Proof. exact (fun_ext (fun z : A => @lem320735 A lt2 x z)). Qed.
Lemma lem320737 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320738 {A : Type'} (lt2 : type1402 A) (x : A) : (term270 A lt2 x) = (term79 A).
Proof. exact (MK_COMB (@lem320737 A) (@lem320736 A lt2 x)). Qed.
Lemma lem320740 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem320741 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (@lem320740 A t). Qed.
Lemma lem320742 {A : Type'} : (term79 A) = True.
Proof. exact (@lem320741 A True). Qed.
Lemma lem320743 {A : Type'} (lt2 : type1402 A) (x : A) : (term270 A lt2 x) = True.
Proof. exact (TRANS (@lem320738 A lt2 x) (@lem320742 A)). Qed.
Lemma lem320744 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem320745 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term271 A P lt2 x) = (term272 A P x).
Proof. exact (MK_COMB (@lem320744 A P x) (@lem320743 A lt2 x)). Qed.
Lemma lem320747 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem320748 {A : Type'} (P : A -> Prop) (x : A) : (term272 A P x) = True.
Proof. exact (@lem320747 (P x)). Qed.
Lemma lem320749 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term271 A P lt2 x) = True.
Proof. exact (TRANS (@lem320745 A lt2 P x) (@lem320748 A P x)). Qed.
Lemma lem320750 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : ((term263 A x) = (term271 A P lt2 x)) = (True = True).
Proof. exact (MK_COMB (@lem320708 A x) (@lem320749 A P lt2 x)). Qed.
Lemma lem320752 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem320753 : (True = True) = True.
Proof. exact (@lem320752 True). Qed.
Lemma lem320754 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : ((term263 A x) = (term271 A P lt2 x)) = True.
Proof. exact (TRANS (@lem320750 A P lt2 x) (@lem320753)). Qed.
Lemma lem320755 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term273 A P lt2) = (term78 A).
Proof. exact (fun_ext (fun x : A => @lem320754 A P lt2 x)). Qed.
Lemma lem320756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320757 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term274 A P lt2) = (term79 A).
Proof. exact (MK_COMB (@lem320756 A) (@lem320755 A P lt2)). Qed.
Lemma lem320759 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem320760 {A : Type'} (t : Prop) : (term80 A t) = t.
Proof. exact (@lem320759 A t). Qed.
Lemma lem320761 {A : Type'} : (term79 A) = True.
Proof. exact (@lem320760 A True). Qed.
Lemma lem320762 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term274 A P lt2) = True.
Proof. exact (TRANS (@lem320757 A P lt2) (@lem320761 A)). Qed.
Lemma lem320763 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term275 A lt2 P) = (term275 A lt2 P).
Proof. exact (eq_refl (term275 A lt2 P)). Qed.
Lemma lem320764 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term276 A P lt2) = (term277 A lt2 P).
Proof. exact (MK_COMB (@lem320763 A lt2 P) (@lem320762 A P lt2)). Qed.
Lemma lem320766 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem320767 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term277 A lt2 P) = (term278 A lt2 P).
Proof. exact (@lem320766 (term278 A lt2 P)). Qed.
Lemma lem320784 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term276 A P lt2) = (term278 A lt2 P).
Proof. exact (TRANS (@lem320764 A lt2 P) (@lem320767 A lt2 P)). Qed.
Lemma lem320785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320786 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term279 A P lt2) = (term280 A lt2 P).
Proof. exact (MK_COMB (@lem320785) (@lem320784 A lt2 P)). Qed.
Lemma lem320790 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem318410 A B f g) (@lem318409 A B f g)). Qed.
Lemma lem320791 {A : Type'} (f : A -> Prop) (g : A -> Prop) : (f = g) = (term281 A f g).
Proof. exact (@lem320790 A Prop f g). Qed.
Lemma lem320792 {A : Type'} (P : A -> Prop) : (P = (term78 A)) = (term282 A P).
Proof. exact (@lem320791 A P (term78 A)). Qed.
Lemma lem320802 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem320803 {A : Type'} (f : A -> Prop) (y : A) : (term23 A f y) = (f y).
Proof. exact (@lem320802 A Prop f y). Qed.
Lemma lem320804 {A : Type'} (x : A) : (term262 A x) = (term263 A x).
Proof. exact (@lem320803 A (term78 A) x). Qed.
Lemma lem320805 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (eq_refl (term263 A x)). Qed.
Lemma lem320806 {A : Type'} : (term264 A) = (term78 A).
Proof. exact (fun_ext (fun x : A => @lem320805 A x)). Qed.
Lemma lem320807 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem320808 {A : Type'} (x : A) : (term262 A x) = (term263 A x).
Proof. exact (MK_COMB (@lem320806 A) (@lem320807 A x)). Qed.
Lemma lem320809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem320810 {A : Type'} (x : A) : (term265 A x) = (term266 A x).
Proof. exact (MK_COMB (@lem320809) (@lem320808 A x)). Qed.
Lemma lem320811 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (eq_refl (term263 A x)). Qed.
Lemma lem320812 {A : Type'} (x : A) : ((term262 A x) = (term263 A x)) = ((term263 A x) = True).
Proof. exact (MK_COMB (@lem320810 A x) (@lem320811 A x)). Qed.
Lemma lem320813 {A : Type'} (x : A) : (term263 A x) = True.
Proof. exact (EQ_MP (@lem320812 A x) (@lem320804 A x)). Qed.
Lemma lem320814 {A : Type'} (P : A -> Prop) (x : A) : (term48 A P x) = (term48 A P x).
Proof. exact (eq_refl (term48 A P x)). Qed.
Lemma lem320815 {A : Type'} (P : A -> Prop) (x : A) : ((P x) = (term263 A x)) = ((P x) = True).
Proof. exact (MK_COMB (@lem320814 A P x) (@lem320813 A x)). Qed.
Lemma lem320817 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem320818 {A : Type'} (P : A -> Prop) (x : A) : ((P x) = True) = (P x).
Proof. exact (@lem320817 (P x)). Qed.
Lemma lem320819 {A : Type'} (P : A -> Prop) (x : A) : ((P x) = (term263 A x)) = (P x).
Proof. exact (TRANS (@lem320815 A P x) (@lem320818 A P x)). Qed.
Lemma lem320820 {A : Type'} (P : A -> Prop) : (term283 A P) = (term284 A P).
Proof. exact (fun_ext (fun x : A => @lem320819 A P x)). Qed.
Lemma lem320821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320822 {A : Type'} (P : A -> Prop) : (term282 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem320821 A) (@lem320820 A P)). Qed.
Lemma lem320827 {A : Type'} (P : A -> Prop) : (P = (term78 A)) = (term72 A P).
Proof. exact (TRANS (@lem320792 A P) (@lem320822 A P)). Qed.
Lemma lem320828 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term261 A lt2 P) = (term285 A lt2 P).
Proof. exact (MK_COMB (@lem320786 A lt2 P) (@lem320827 A P)). Qed.
Lemma lem320831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320832 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term286 A lt2 P) = (term287 A lt2 P).
Proof. exact (MK_COMB (@lem320831) (@lem320828 A lt2 P)). Qed.
Lemma lem320837 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem320838 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term288 A lt2 P) = (term289 A lt2 P).
Proof. exact (MK_COMB (@lem320832 A lt2 P) (@lem320837 A P)). Qed.
Lemma lem320841 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term289 A lt2 P) = (term288 A lt2 P).
Proof. exact (SYM (@lem320838 A lt2 P)). Qed.
Lemma lem320843 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem320844 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term289 A lt2 P) = (term290 A lt2 P).
Proof. exact (@lem320843 (term289 A lt2 P)). Qed.
Lemma lem320845 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term290 A lt2 P) = (term289 A lt2 P).
Proof. exact (SYM (@lem320844 A lt2 P)). Qed.
Lemma lem320846 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term291 A lt2 P) : term291 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem320849 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term292 A lt2 P) : term292 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem320850 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term293 A lt2 P.
Proof. exact (fun h0 : term292 A lt2 P => @lem320849 A lt2 P h0). Qed.
Lemma lem320851 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term293 A lt2 P) : term293 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem320852 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term292 A lt2 P) : term292 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem320853 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term292 A lt2 P) (h2 : term293 A lt2 P) : term292 A lt2 P.
Proof. exact (@lem320851 A lt2 P h2 (@lem320852 A lt2 P h1)). Qed.
Lemma lem320854 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term292 A lt2 P) : term294 A lt2 P.
Proof. exact (fun h0 : term293 A lt2 P => @lem320853 A lt2 P h1 h0). Qed.
Lemma lem320855 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term293 A lt2 P) : term293 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem320856 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term292 A lt2 P) (h2 : term293 A lt2 P) : term292 A lt2 P.
Proof. exact (@lem320854 A lt2 P h1 (@lem320855 A lt2 P h2)). Qed.
Lemma lem320857 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term293 A lt2 P) : term293 A lt2 P.
Proof. exact (fun h0 : term292 A lt2 P => @lem320856 A lt2 P h0 h1). Qed.
Lemma lem320858 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term295 A lt2 P.
Proof. exact (fun h0 : term293 A lt2 P => @lem320857 A lt2 P h0). Qed.
Lemma lem320861 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term293 A lt2 P.
Proof. exact (@lem320858 A lt2 P (@lem320850 A lt2 P)). Qed.
Lemma lem320862 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term293 A lt2 P.
Proof. exact (@lem320861 A lt2 P). Qed.
Lemma lem320886 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem320887 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term290 A lt2 P) = (term296 A lt2 P).
Proof. exact (@lem320886 (term291 A lt2 P)). Qed.
Lemma lem320889 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem320890 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term296 A lt2 P) = (term289 A lt2 P).
Proof. exact (@lem320889 (term289 A lt2 P)). Qed.
Lemma lem320893 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term290 A lt2 P) = (term289 A lt2 P).
Proof. exact (TRANS (@lem320887 A lt2 P) (@lem320890 A lt2 P)). Qed.
Lemma lem320916 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term297 A lt2 P) = (term297 A lt2 P).
Proof. exact (eq_refl (term297 A lt2 P)). Qed.
Lemma lem320917 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term292 A lt2 P) = (term298 A lt2 P).
Proof. exact (MK_COMB (@lem320916 A lt2 P) (@lem320893 A lt2 P)). Qed.
Lemma lem320920 {A : Type'} (P : A -> Prop) : (term299 A P) = (term300 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem320917 A lt2 P)). Qed.
Lemma lem320921 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem320922 {A : Type'} (P : A -> Prop) : (term301 A P) = (term302 A P).
Proof. exact (MK_COMB (@lem320921 A) (@lem320920 A P)). Qed.
Lemma lem320927 {A : Type'} : (term303 A) = (term304 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem320922 A P)). Qed.
Lemma lem320928 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem320937 {A : Type'} : (term305 A) = (term306 A).
Proof. exact (MK_COMB (@lem320928 A) (@lem320927 A)). Qed.
Lemma lem320938 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem320939 {A : Type'} (P : A -> Prop) : (term284 A P) = (term284 A P).
Proof. exact (fun_ext (fun x : A => @lem320938 A P x)). Qed.
Lemma lem320940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320941 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem320940 A) (@lem320939 A P)). Qed.
Lemma lem320942 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem320943 {A : Type'} (P : A -> Prop) : (term284 A P) = (term284 A P).
Proof. exact (fun_ext (fun x : A => @lem320942 A P x)). Qed.
Lemma lem320944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320945 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem320944 A) (@lem320943 A P)). Qed.
Lemma lem320950 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term103 A lt2 x P z) = (term103 A lt2 x P z).
Proof. exact (eq_refl (term103 A lt2 x P z)). Qed.
Lemma lem320951 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term104 A lt2 x P) = (term104 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem320950 A lt2 x P z)). Qed.
Lemma lem320952 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320953 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term105 A lt2 x P) = (term105 A lt2 x P).
Proof. exact (MK_COMB (@lem320952 A) (@lem320951 A lt2 x P)). Qed.
Lemma lem320956 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem320957 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term307 A lt2 x P) = (term307 A lt2 x P).
Proof. exact (MK_COMB (@lem320956 A P x) (@lem320953 A lt2 x P)). Qed.
Lemma lem320960 {A : Type'} (P : A -> Prop) (x : A) : (term48 A P x) = (term48 A P x).
Proof. exact (eq_refl (term48 A P x)). Qed.
Lemma lem320961 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((P x) = (term307 A lt2 x P)) = ((P x) = (term307 A lt2 x P)).
Proof. exact (MK_COMB (@lem320960 A P x) (@lem320957 A lt2 x P)). Qed.
Lemma lem320962 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term308 A lt2 P) = (term308 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem320961 A lt2 x P)). Qed.
Lemma lem320963 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320964 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term278 A lt2 P) = (term278 A lt2 P).
Proof. exact (MK_COMB (@lem320963 A) (@lem320962 A lt2 P)). Qed.
Lemma lem320965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320966 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term280 A lt2 P) = (term280 A lt2 P).
Proof. exact (MK_COMB (@lem320965) (@lem320964 A lt2 P)). Qed.
Lemma lem320967 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term285 A lt2 P) = (term285 A lt2 P).
Proof. exact (MK_COMB (@lem320966 A lt2 P) (@lem320945 A P)). Qed.
Lemma lem320968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320969 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term287 A lt2 P) = (term287 A lt2 P).
Proof. exact (MK_COMB (@lem320968) (@lem320967 A lt2 P)). Qed.
Lemma lem320970 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term289 A lt2 P) = (term289 A lt2 P).
Proof. exact (MK_COMB (@lem320969 A lt2 P) (@lem320941 A P)). Qed.
Lemma lem320971 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem320976 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term103 A lt2 x P y) = (term103 A lt2 x P y).
Proof. exact (eq_refl (term103 A lt2 x P y)). Qed.
Lemma lem320977 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term104 A lt2 x P) = (term104 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem320976 A lt2 x P y)). Qed.
Lemma lem320978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320979 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term105 A lt2 x P) = (term105 A lt2 x P).
Proof. exact (MK_COMB (@lem320978 A) (@lem320977 A lt2 x P)). Qed.
Lemma lem320980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320981 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term309 A lt2 x P) = (term309 A lt2 x P).
Proof. exact (MK_COMB (@lem320980) (@lem320979 A lt2 x P)). Qed.
Lemma lem320982 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term310 A lt2 P x) = (term310 A lt2 P x).
Proof. exact (MK_COMB (@lem320981 A lt2 x P) (@lem320971 A P x)). Qed.
Lemma lem320983 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term311 A lt2 P) = (term311 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem320982 A lt2 P x)). Qed.
Lemma lem320984 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem320985 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term9 A lt2 P).
Proof. exact (MK_COMB (@lem320984 A) (@lem320983 A lt2 P)). Qed.
Lemma lem320986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem320987 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term297 A lt2 P) = (term297 A lt2 P).
Proof. exact (MK_COMB (@lem320986) (@lem320985 A lt2 P)). Qed.
Lemma lem320988 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term298 A lt2 P) = (term298 A lt2 P).
Proof. exact (MK_COMB (@lem320987 A lt2 P) (@lem320970 A lt2 P)). Qed.
Lemma lem320989 {A : Type'} (P : A -> Prop) : (term300 A P) = (term300 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem320988 A lt2 P)). Qed.
Lemma lem320990 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem320991 {A : Type'} (P : A -> Prop) : (term302 A P) = (term302 A P).
Proof. exact (MK_COMB (@lem320990 A) (@lem320989 A P)). Qed.
Lemma lem320992 {A : Type'} : (term304 A) = (term304 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem320991 A P)). Qed.
Lemma lem320993 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem320994 {A : Type'} : (term306 A) = (term306 A).
Proof. exact (MK_COMB (@lem320993 A) (@lem320992 A)). Qed.
Lemma lem321059 {A : Type'} : (term305 A) = (term306 A).
Proof. exact (TRANS (@lem320937 A) (@lem320994 A)). Qed.
Lemma lem321060 {A : Type'} : (term306 A) = (term305 A).
Proof. exact (SYM (@lem321059 A)). Qed.
Lemma lem321061 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem321062 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term285 A lt2 P) : term285 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem321064 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem321065 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (term312 A P x).
Proof. exact (@lem321064 (P x)). Qed.
Lemma lem321066 {A : Type'} (P : A -> Prop) (x : A) : (term312 A P x) = (P x).
Proof. exact (SYM (@lem321065 A P x)). Qed.
Lemma lem321067 {A : Type'} (P : A -> Prop) (x : A) (h1 : term153 A P x) : term153 A P x.
Proof. exact (h1). Qed.
Lemma lem321074 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term118 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (P y)). Qed.
Lemma lem321075 {A : Type'} (P : A -> Prop) : (term121 A P) = (term122 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem321076 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term123 A lt2 x P) = (term124 A lt2 x P).
Proof. exact (@lem321075 A (term104 A lt2 x P)). Qed.
Lemma lem321077 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term125 A lt2 x P y) = (term103 A lt2 x P y).
Proof. exact (eq_refl (term125 A lt2 x P y)). Qed.
Lemma lem321078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem321079 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term126 A lt2 x P y) = (term118 A lt2 x P y).
Proof. exact (MK_COMB (@lem321078) (@lem321077 A lt2 x P y)). Qed.
Lemma lem321080 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term126 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (TRANS (@lem321079 A lt2 x P y) (@lem321074 A lt2 x P y)). Qed.
Lemma lem321081 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term127 A lt2 x P) = (term128 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem321080 A lt2 x P y)). Qed.
Lemma lem321082 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321083 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term124 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (MK_COMB (@lem321082 A) (@lem321081 A lt2 x P)). Qed.
Lemma lem321084 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term123 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (TRANS (@lem321076 A lt2 x P) (@lem321083 A lt2 x P)). Qed.
Lemma lem321085 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem321086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321087 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term313 A lt2 x P) = (term314 A lt2 x P).
Proof. exact (MK_COMB (@lem321086) (@lem321084 A lt2 x P)). Qed.
Lemma lem321088 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term315 A lt2 P x) = (term316 A lt2 P x).
Proof. exact (MK_COMB (@lem321087 A lt2 x P) (@lem321085 A P x)). Qed.
Lemma lem321089 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term310 A lt2 P x) = (term315 A lt2 P x).
Proof. exact (@lem17265 (term105 A lt2 x P) (P x)). Qed.
Lemma lem321090 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term310 A lt2 P x) = (term316 A lt2 P x).
Proof. exact (TRANS (@lem321089 A lt2 P x) (@lem321088 A lt2 P x)). Qed.
Lemma lem321091 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term311 A lt2 P) = (term317 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321090 A lt2 P x)). Qed.
Lemma lem321092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321093 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term318 A lt2 P).
Proof. exact (MK_COMB (@lem321092 A) (@lem321091 A lt2 P)). Qed.
Lemma lem321176 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem321177 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem321176 A P Q). Qed.
Lemma lem321178 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term321 A lt2 P x) = (term322 A lt2 P x).
Proof. exact (@lem321177 A (term128 A lt2 x P) (P x)). Qed.
Lemma lem321179 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term154 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (eq_refl (term154 A lt2 x P y)). Qed.
Lemma lem321180 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 x P) = (term128 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem321179 A lt2 x P y)). Qed.
Lemma lem321181 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321182 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term156 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (MK_COMB (@lem321181 A) (@lem321180 A lt2 x P)). Qed.
Lemma lem321183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321184 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term323 A lt2 x P) = (term314 A lt2 x P).
Proof. exact (MK_COMB (@lem321183) (@lem321182 A lt2 x P)). Qed.
Lemma lem321185 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem321186 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term321 A lt2 P x) = (term316 A lt2 P x).
Proof. exact (MK_COMB (@lem321184 A lt2 x P) (@lem321185 A P x)). Qed.
Lemma lem321187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321188 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term324 A lt2 P x) = (term325 A lt2 P x).
Proof. exact (MK_COMB (@lem321187) (@lem321186 A lt2 P x)). Qed.
Lemma lem321189 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term154 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (eq_refl (term154 A lt2 x P y)). Qed.
Lemma lem321190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321191 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term326 A lt2 x P y) = (term327 A lt2 x P y).
Proof. exact (MK_COMB (@lem321190) (@lem321189 A lt2 x P y)). Qed.
Lemma lem321192 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem321193 {A : Type'} (lt2 : type1402 A) (y : A) (P : A -> Prop) (x : A) : (term328 A lt2 y P x) = (term329 A lt2 y P x).
Proof. exact (MK_COMB (@lem321191 A lt2 x P y) (@lem321192 A P x)). Qed.
Lemma lem321194 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term330 A lt2 P x) = (term331 A lt2 P x).
Proof. exact (fun_ext (fun y : A => @lem321193 A lt2 y P x)). Qed.
Lemma lem321195 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321196 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term322 A lt2 P x) = (term332 A lt2 P x).
Proof. exact (MK_COMB (@lem321195 A) (@lem321194 A lt2 P x)). Qed.
Lemma lem321197 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : ((term321 A lt2 P x) = (term322 A lt2 P x)) = ((term316 A lt2 P x) = (term332 A lt2 P x)).
Proof. exact (MK_COMB (@lem321188 A lt2 P x) (@lem321196 A lt2 P x)). Qed.
Lemma lem321198 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term316 A lt2 P x) = (term332 A lt2 P x).
Proof. exact (EQ_MP (@lem321197 A lt2 P x) (@lem321178 A lt2 P x)). Qed.
Lemma lem321199 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term317 A lt2 P) = (term333 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321198 A lt2 P x)). Qed.
Lemma lem321200 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321201 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term318 A lt2 P) = (term334 A lt2 P).
Proof. exact (MK_COMB (@lem321200 A) (@lem321199 A lt2 P)). Qed.
Lemma lem321203 {A B : Type'} (P : type1413 A B) : (term335 A B P) = (term336 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem321204 {A : Type'} (P : type1402 A) : (term337 A P) = (term338 A P).
Proof. exact (@lem321203 A A P). Qed.
Lemma lem321205 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term339 A lt2 P) = (term340 A lt2 P).
Proof. exact (@lem321204 A (term341 A lt2 P)). Qed.
Lemma lem321206 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term342 A lt2 P x) = (term331 A lt2 P x).
Proof. exact (eq_refl (term342 A lt2 P x)). Qed.
Lemma lem321207 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem321208 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) (y : A) : (term343 A lt2 P x y) = (term344 A lt2 P x y).
Proof. exact (MK_COMB (@lem321206 A lt2 P x) (@lem321207 A y)). Qed.
Lemma lem321209 {A : Type'} (lt2 : type1402 A) (y : A) (P : A -> Prop) (x : A) : (term344 A lt2 P x y) = (term329 A lt2 y P x).
Proof. exact (eq_refl (term344 A lt2 P x y)). Qed.
Lemma lem321210 {A : Type'} (lt2 : type1402 A) (y : A) (P : A -> Prop) (x : A) : (term343 A lt2 P x y) = (term329 A lt2 y P x).
Proof. exact (TRANS (@lem321208 A lt2 P x y) (@lem321209 A lt2 y P x)). Qed.
Lemma lem321211 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term345 A lt2 P x) = (term331 A lt2 P x).
Proof. exact (fun_ext (fun y : A => @lem321210 A lt2 y P x)). Qed.
Lemma lem321212 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321213 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term346 A lt2 P x) = (term332 A lt2 P x).
Proof. exact (MK_COMB (@lem321212 A) (@lem321211 A lt2 P x)). Qed.
Lemma lem321214 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term347 A lt2 P) = (term333 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321213 A lt2 P x)). Qed.
Lemma lem321215 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321216 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term339 A lt2 P) = (term334 A lt2 P).
Proof. exact (MK_COMB (@lem321215 A) (@lem321214 A lt2 P)). Qed.
Lemma lem321217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321218 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term348 A lt2 P) = (term349 A lt2 P).
Proof. exact (MK_COMB (@lem321217) (@lem321216 A lt2 P)). Qed.
Lemma lem321219 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term342 A lt2 P x) = (term331 A lt2 P x).
Proof. exact (eq_refl (term342 A lt2 P x)). Qed.
Lemma lem321220 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem321221 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term350 A lt2 P y x) = (term351 A lt2 P y x).
Proof. exact (MK_COMB (@lem321219 A lt2 P x) (@lem321220 A y x)). Qed.
Lemma lem321222 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term351 A lt2 P y x) = (term352 A lt2 y P x).
Proof. exact (eq_refl (term351 A lt2 P y x)). Qed.
Lemma lem321223 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term350 A lt2 P y x) = (term352 A lt2 y P x).
Proof. exact (TRANS (@lem321221 A lt2 P y x) (@lem321222 A lt2 y P x)). Qed.
Lemma lem321224 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term353 A lt2 P y) = (term354 A lt2 y P).
Proof. exact (fun_ext (fun x : A => @lem321223 A lt2 y P x)). Qed.
Lemma lem321225 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321226 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term355 A lt2 P y) = (term356 A lt2 y P).
Proof. exact (MK_COMB (@lem321225 A) (@lem321224 A lt2 y P)). Qed.
Lemma lem321227 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term357 A lt2 P) = (term358 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem321226 A lt2 y P)). Qed.
Lemma lem321228 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem321229 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term340 A lt2 P) = (term359 A lt2 P).
Proof. exact (MK_COMB (@lem321228 A) (@lem321227 A lt2 P)). Qed.
Lemma lem321230 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term339 A lt2 P) = (term340 A lt2 P)) = ((term334 A lt2 P) = (term359 A lt2 P)).
Proof. exact (MK_COMB (@lem321218 A lt2 P) (@lem321229 A lt2 P)). Qed.
Lemma lem321231 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term334 A lt2 P) = (term359 A lt2 P).
Proof. exact (EQ_MP (@lem321230 A lt2 P) (@lem321205 A lt2 P)). Qed.
Lemma lem321233 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term318 A lt2 P) = (term359 A lt2 P).
Proof. exact (TRANS (@lem321201 A lt2 P) (@lem321231 A lt2 P)). Qed.
Lemma lem321234 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term359 A lt2 P).
Proof. exact (TRANS (@lem321093 A lt2 P) (@lem321233 A lt2 P)). Qed.
Lemma lem321235 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term359 A lt2 P.
Proof. exact (EQ_MP (@lem321234 A lt2 P) (@lem321061 A lt2 P h1)). Qed.
Lemma lem321248 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term118 A lt2 x P z) = (term119 A lt2 x P z).
Proof. exact (@lem17362 (lt2 z x) (P z)). Qed.
Lemma lem321253 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term103 A lt2 x P z) = (term120 A lt2 x P z).
Proof. exact (@lem17265 (lt2 z x) (P z)). Qed.
Lemma lem321254 {A : Type'} (P : A -> Prop) : (term121 A P) = (term122 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem321255 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term123 A lt2 x P) = (term124 A lt2 x P).
Proof. exact (@lem321254 A (term104 A lt2 x P)). Qed.
Lemma lem321256 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term125 A lt2 x P z) = (term103 A lt2 x P z).
Proof. exact (eq_refl (term125 A lt2 x P z)). Qed.
Lemma lem321257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem321258 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term126 A lt2 x P z) = (term118 A lt2 x P z).
Proof. exact (MK_COMB (@lem321257) (@lem321256 A lt2 x P z)). Qed.
Lemma lem321259 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term126 A lt2 x P z) = (term119 A lt2 x P z).
Proof. exact (TRANS (@lem321258 A lt2 x P z) (@lem321248 A lt2 x P z)). Qed.
Lemma lem321260 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term127 A lt2 x P) = (term128 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321259 A lt2 x P z)). Qed.
Lemma lem321261 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321262 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term124 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (MK_COMB (@lem321261 A) (@lem321260 A lt2 x P)). Qed.
Lemma lem321263 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term123 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (TRANS (@lem321255 A lt2 x P) (@lem321262 A lt2 x P)). Qed.
Lemma lem321264 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term104 A lt2 x P) = (term130 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321253 A lt2 x P z)). Qed.
Lemma lem321265 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321266 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term105 A lt2 x P) = (term131 A lt2 x P).
Proof. exact (MK_COMB (@lem321265 A) (@lem321264 A lt2 x P)). Qed.
Lemma lem321268 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem321269 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term360 A lt2 x P) = (term361 A lt2 x P).
Proof. exact (MK_COMB (@lem321268 A P x) (@lem321263 A lt2 x P)). Qed.
Lemma lem321270 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term362 A lt2 x P) = (term360 A lt2 x P).
Proof. exact (@lem17160 (P x) (term105 A lt2 x P)). Qed.
Lemma lem321271 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term362 A lt2 x P) = (term361 A lt2 x P).
Proof. exact (TRANS (@lem321270 A lt2 x P) (@lem321269 A lt2 x P)). Qed.
Lemma lem321273 {A : Type'} (P : A -> Prop) (x : A) : (term106 A P x) = (term106 A P x).
Proof. exact (eq_refl (term106 A P x)). Qed.
Lemma lem321274 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term307 A lt2 x P) = (term363 A lt2 x P).
Proof. exact (MK_COMB (@lem321273 A P x) (@lem321266 A lt2 x P)). Qed.
Lemma lem321276 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem321277 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term364 A lt2 x P) = (term365 A lt2 x P).
Proof. exact (MK_COMB (@lem321276 A P x) (@lem321274 A lt2 x P)). Qed.
Lemma lem321279 {A : Type'} (P : A -> Prop) (x : A) : (term366 A P x) = (term366 A P x).
Proof. exact (eq_refl (term366 A P x)). Qed.
Lemma lem321280 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term367 A lt2 x P) = (term368 A lt2 x P).
Proof. exact (MK_COMB (@lem321279 A P x) (@lem321271 A lt2 x P)). Qed.
Lemma lem321281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321282 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term369 A lt2 x P) = (term370 A lt2 x P).
Proof. exact (MK_COMB (@lem321281) (@lem321280 A lt2 x P)). Qed.
Lemma lem321283 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term371 A lt2 x P) = (term372 A lt2 x P).
Proof. exact (MK_COMB (@lem321282 A lt2 x P) (@lem321277 A lt2 x P)). Qed.
Lemma lem321284 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term373 A lt2 x P) = (term371 A lt2 x P).
Proof. exact (@lem17646 (P x) (term307 A lt2 x P)). Qed.
Lemma lem321285 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term373 A lt2 x P) = (term372 A lt2 x P).
Proof. exact (TRANS (@lem321284 A lt2 x P) (@lem321283 A lt2 x P)). Qed.
Lemma lem321286 {A : Type'} (P : A -> Prop) : (term121 A P) = (term122 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem321287 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term374 A lt2 P) = (term375 A lt2 P).
Proof. exact (@lem321286 A (term308 A lt2 P)). Qed.
Lemma lem321288 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term376 A lt2 P x) = ((P x) = (term307 A lt2 x P)).
Proof. exact (eq_refl (term376 A lt2 P x)). Qed.
Lemma lem321289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem321290 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term377 A lt2 P x) = (term373 A lt2 x P).
Proof. exact (MK_COMB (@lem321289) (@lem321288 A lt2 x P)). Qed.
Lemma lem321291 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term377 A lt2 P x) = (term372 A lt2 x P).
Proof. exact (TRANS (@lem321290 A lt2 x P) (@lem321285 A lt2 x P)). Qed.
Lemma lem321292 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term378 A lt2 P) = (term379 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321291 A lt2 x P)). Qed.
Lemma lem321293 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321294 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term375 A lt2 P) = (term380 A lt2 P).
Proof. exact (MK_COMB (@lem321293 A) (@lem321292 A lt2 P)). Qed.
Lemma lem321295 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term374 A lt2 P) = (term380 A lt2 P).
Proof. exact (TRANS (@lem321287 A lt2 P) (@lem321294 A lt2 P)). Qed.
Lemma lem321296 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem321297 {A : Type'} (P : A -> Prop) : (term284 A P) = (term284 A P).
Proof. exact (fun_ext (fun x : A => @lem321296 A P x)). Qed.
Lemma lem321298 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321299 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem321298 A) (@lem321297 A P)). Qed.
Lemma lem321300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321301 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term381 A lt2 P) = (term382 A lt2 P).
Proof. exact (MK_COMB (@lem321300) (@lem321295 A lt2 P)). Qed.
Lemma lem321302 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term383 A lt2 P) = (term384 A lt2 P).
Proof. exact (MK_COMB (@lem321301 A lt2 P) (@lem321299 A P)). Qed.
Lemma lem321303 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term285 A lt2 P) = (term383 A lt2 P).
Proof. exact (@lem17265 (term278 A lt2 P) (term72 A P)). Qed.
Lemma lem321304 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term285 A lt2 P) = (term384 A lt2 P).
Proof. exact (TRANS (@lem321303 A lt2 P) (@lem321302 A lt2 P)). Qed.
Lemma lem321306 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem321307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term195 A P Q).
Proof. exact (@lem321306 A P Q). Qed.
Lemma lem321308 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term385 A lt2 P) = (term386 A lt2 P).
Proof. exact (@lem321307 A (term387 A lt2 P) (term388 A lt2 P)). Qed.
Lemma lem321309 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term389 A lt2 P x) = (term368 A lt2 x P).
Proof. exact (eq_refl (term389 A lt2 P x)). Qed.
Lemma lem321310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321311 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term390 A lt2 P x) = (term370 A lt2 x P).
Proof. exact (MK_COMB (@lem321310) (@lem321309 A lt2 x P)). Qed.
Lemma lem321312 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term391 A lt2 P x) = (term365 A lt2 x P).
Proof. exact (eq_refl (term391 A lt2 P x)). Qed.
Lemma lem321313 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term392 A lt2 P x) = (term372 A lt2 x P).
Proof. exact (MK_COMB (@lem321311 A lt2 x P) (@lem321312 A lt2 x P)). Qed.
Lemma lem321314 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term393 A lt2 P) = (term379 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321313 A lt2 x P)). Qed.
Lemma lem321315 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321316 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term385 A lt2 P) = (term380 A lt2 P).
Proof. exact (MK_COMB (@lem321315 A) (@lem321314 A lt2 P)). Qed.
Lemma lem321317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321318 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term394 A lt2 P) = (term395 A lt2 P).
Proof. exact (MK_COMB (@lem321317) (@lem321316 A lt2 P)). Qed.
Lemma lem321319 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term389 A lt2 P x) = (term368 A lt2 x P).
Proof. exact (eq_refl (term389 A lt2 P x)). Qed.
Lemma lem321320 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term396 A lt2 P) = (term387 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321319 A lt2 x P)). Qed.
Lemma lem321321 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321322 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term397 A lt2 P) = (term398 A lt2 P).
Proof. exact (MK_COMB (@lem321321 A) (@lem321320 A lt2 P)). Qed.
Lemma lem321323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321324 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term399 A lt2 P) = (term400 A lt2 P).
Proof. exact (MK_COMB (@lem321323) (@lem321322 A lt2 P)). Qed.
Lemma lem321325 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term391 A lt2 P x) = (term365 A lt2 x P).
Proof. exact (eq_refl (term391 A lt2 P x)). Qed.
Lemma lem321326 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term401 A lt2 P) = (term388 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321325 A lt2 x P)). Qed.
Lemma lem321327 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321328 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term402 A lt2 P) = (term403 A lt2 P).
Proof. exact (MK_COMB (@lem321327 A) (@lem321326 A lt2 P)). Qed.
Lemma lem321329 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term386 A lt2 P) = (term404 A lt2 P).
Proof. exact (MK_COMB (@lem321324 A lt2 P) (@lem321328 A lt2 P)). Qed.
Lemma lem321330 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term385 A lt2 P) = (term386 A lt2 P)) = ((term380 A lt2 P) = (term404 A lt2 P)).
Proof. exact (MK_COMB (@lem321318 A lt2 P) (@lem321329 A lt2 P)). Qed.
Lemma lem321331 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term380 A lt2 P) = (term404 A lt2 P).
Proof. exact (EQ_MP (@lem321330 A lt2 P) (@lem321308 A lt2 P)). Qed.
Lemma lem321488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321489 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term382 A lt2 P) = (term405 A lt2 P).
Proof. exact (MK_COMB (@lem321488) (@lem321331 A lt2 P)). Qed.
Lemma lem321494 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem321495 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term384 A lt2 P) = (term406 A lt2 P).
Proof. exact (MK_COMB (@lem321489 A lt2 P) (@lem321494 A P)). Qed.
Lemma lem321497 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem321498 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem321497 A P Q). Qed.
Lemma lem321499 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term407 A lt2 x P) = (term408 A lt2 x P).
Proof. exact (@lem321498 A (term153 A P x) (term128 A lt2 x P)). Qed.
Lemma lem321500 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term154 A lt2 x P z) = (term119 A lt2 x P z).
Proof. exact (eq_refl (term154 A lt2 x P z)). Qed.
Lemma lem321501 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term155 A lt2 x P) = (term128 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321500 A lt2 x P z)). Qed.
Lemma lem321502 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321503 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term156 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (MK_COMB (@lem321502 A) (@lem321501 A lt2 x P)). Qed.
Lemma lem321504 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem321505 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term407 A lt2 x P) = (term361 A lt2 x P).
Proof. exact (MK_COMB (@lem321504 A P x) (@lem321503 A lt2 x P)). Qed.
Lemma lem321506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321507 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term409 A lt2 x P) = (term410 A lt2 x P).
Proof. exact (MK_COMB (@lem321506) (@lem321505 A lt2 x P)). Qed.
Lemma lem321508 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term154 A lt2 x P z) = (term119 A lt2 x P z).
Proof. exact (eq_refl (term154 A lt2 x P z)). Qed.
Lemma lem321509 {A : Type'} (P : A -> Prop) (x : A) : (term132 A P x) = (term132 A P x).
Proof. exact (eq_refl (term132 A P x)). Qed.
Lemma lem321510 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term411 A lt2 x P z) = (term412 A lt2 x P z).
Proof. exact (MK_COMB (@lem321509 A P x) (@lem321508 A lt2 x P z)). Qed.
Lemma lem321511 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term413 A lt2 x P) = (term414 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321510 A lt2 x P z)). Qed.
Lemma lem321512 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321513 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term408 A lt2 x P) = (term415 A lt2 x P).
Proof. exact (MK_COMB (@lem321512 A) (@lem321511 A lt2 x P)). Qed.
Lemma lem321514 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term407 A lt2 x P) = (term408 A lt2 x P)) = ((term361 A lt2 x P) = (term415 A lt2 x P)).
Proof. exact (MK_COMB (@lem321507 A lt2 x P) (@lem321513 A lt2 x P)). Qed.
Lemma lem321515 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term361 A lt2 x P) = (term415 A lt2 x P).
Proof. exact (EQ_MP (@lem321514 A lt2 x P) (@lem321499 A lt2 x P)). Qed.
Lemma lem321516 {A : Type'} (P : A -> Prop) (x : A) : (term366 A P x) = (term366 A P x).
Proof. exact (eq_refl (term366 A P x)). Qed.
Lemma lem321517 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term368 A lt2 x P) = (term416 A lt2 x P).
Proof. exact (MK_COMB (@lem321516 A P x) (@lem321515 A lt2 x P)). Qed.
Lemma lem321519 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem321520 {A : Type'} (P : Prop) (Q : A -> Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (@lem321519 A P Q). Qed.
Lemma lem321521 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term417 A lt2 x P) = (term418 A lt2 x P).
Proof. exact (@lem321520 A (P x) (term414 A lt2 x P)). Qed.
Lemma lem321522 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term419 A lt2 x P z) = (term412 A lt2 x P z).
Proof. exact (eq_refl (term419 A lt2 x P z)). Qed.
Lemma lem321523 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term420 A lt2 x P) = (term414 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321522 A lt2 x P z)). Qed.
Lemma lem321524 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321525 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term421 A lt2 x P) = (term415 A lt2 x P).
Proof. exact (MK_COMB (@lem321524 A) (@lem321523 A lt2 x P)). Qed.
Lemma lem321526 {A : Type'} (P : A -> Prop) (x : A) : (term366 A P x) = (term366 A P x).
Proof. exact (eq_refl (term366 A P x)). Qed.
Lemma lem321527 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term417 A lt2 x P) = (term416 A lt2 x P).
Proof. exact (MK_COMB (@lem321526 A P x) (@lem321525 A lt2 x P)). Qed.
Lemma lem321528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321529 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term422 A lt2 x P) = (term423 A lt2 x P).
Proof. exact (MK_COMB (@lem321528) (@lem321527 A lt2 x P)). Qed.
Lemma lem321530 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term419 A lt2 x P z) = (term412 A lt2 x P z).
Proof. exact (eq_refl (term419 A lt2 x P z)). Qed.
Lemma lem321531 {A : Type'} (P : A -> Prop) (x : A) : (term366 A P x) = (term366 A P x).
Proof. exact (eq_refl (term366 A P x)). Qed.
Lemma lem321532 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term424 A lt2 x P z) = (term425 A lt2 x P z).
Proof. exact (MK_COMB (@lem321531 A P x) (@lem321530 A lt2 x P z)). Qed.
Lemma lem321533 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term426 A lt2 x P) = (term427 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321532 A lt2 x P z)). Qed.
Lemma lem321534 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321535 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term418 A lt2 x P) = (term428 A lt2 x P).
Proof. exact (MK_COMB (@lem321534 A) (@lem321533 A lt2 x P)). Qed.
Lemma lem321536 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term417 A lt2 x P) = (term418 A lt2 x P)) = ((term416 A lt2 x P) = (term428 A lt2 x P)).
Proof. exact (MK_COMB (@lem321529 A lt2 x P) (@lem321535 A lt2 x P)). Qed.
Lemma lem321537 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term416 A lt2 x P) = (term428 A lt2 x P).
Proof. exact (EQ_MP (@lem321536 A lt2 x P) (@lem321521 A lt2 x P)). Qed.
Lemma lem321538 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term368 A lt2 x P) = (term428 A lt2 x P).
Proof. exact (TRANS (@lem321517 A lt2 x P) (@lem321537 A lt2 x P)). Qed.
Lemma lem321539 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term387 A lt2 P) = (term429 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321538 A lt2 x P)). Qed.
Lemma lem321540 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321541 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term398 A lt2 P) = (term430 A lt2 P).
Proof. exact (MK_COMB (@lem321540 A) (@lem321539 A lt2 P)). Qed.
Lemma lem321542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321543 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term400 A lt2 P) = (term431 A lt2 P).
Proof. exact (MK_COMB (@lem321542) (@lem321541 A lt2 P)). Qed.
Lemma lem321544 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term403 A lt2 P) = (term403 A lt2 P).
Proof. exact (eq_refl (term403 A lt2 P)). Qed.
Lemma lem321545 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term404 A lt2 P) = (term432 A lt2 P).
Proof. exact (MK_COMB (@lem321543 A lt2 P) (@lem321544 A lt2 P)). Qed.
Lemma lem321547 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem321548 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (@lem321547 A P Q). Qed.
Lemma lem321549 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term433 A lt2 P) = (term434 A lt2 P).
Proof. exact (@lem321548 A (term429 A lt2 P) (term388 A lt2 P)). Qed.
Lemma lem321550 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term435 A lt2 P x) = (term428 A lt2 x P).
Proof. exact (eq_refl (term435 A lt2 P x)). Qed.
Lemma lem321551 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term436 A lt2 P) = (term429 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321550 A lt2 x P)). Qed.
Lemma lem321552 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321553 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term437 A lt2 P) = (term430 A lt2 P).
Proof. exact (MK_COMB (@lem321552 A) (@lem321551 A lt2 P)). Qed.
Lemma lem321554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321555 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term438 A lt2 P) = (term431 A lt2 P).
Proof. exact (MK_COMB (@lem321554) (@lem321553 A lt2 P)). Qed.
Lemma lem321556 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term391 A lt2 P x) = (term365 A lt2 x P).
Proof. exact (eq_refl (term391 A lt2 P x)). Qed.
Lemma lem321557 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term401 A lt2 P) = (term388 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321556 A lt2 x P)). Qed.
Lemma lem321558 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321559 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term402 A lt2 P) = (term403 A lt2 P).
Proof. exact (MK_COMB (@lem321558 A) (@lem321557 A lt2 P)). Qed.
Lemma lem321560 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term433 A lt2 P) = (term432 A lt2 P).
Proof. exact (MK_COMB (@lem321555 A lt2 P) (@lem321559 A lt2 P)). Qed.
Lemma lem321561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321562 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term439 A lt2 P) = (term440 A lt2 P).
Proof. exact (MK_COMB (@lem321561) (@lem321560 A lt2 P)). Qed.
Lemma lem321563 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term435 A lt2 P x) = (term428 A lt2 x P).
Proof. exact (eq_refl (term435 A lt2 P x)). Qed.
Lemma lem321564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321565 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term441 A lt2 P x) = (term442 A lt2 x P).
Proof. exact (MK_COMB (@lem321564) (@lem321563 A lt2 x P)). Qed.
Lemma lem321566 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term391 A lt2 P x) = (term365 A lt2 x P).
Proof. exact (eq_refl (term391 A lt2 P x)). Qed.
Lemma lem321567 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term443 A lt2 P x) = (term444 A lt2 x P).
Proof. exact (MK_COMB (@lem321565 A lt2 x P) (@lem321566 A lt2 x P)). Qed.
Lemma lem321568 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term445 A lt2 P) = (term446 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321567 A lt2 x P)). Qed.
Lemma lem321569 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321570 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term434 A lt2 P) = (term447 A lt2 P).
Proof. exact (MK_COMB (@lem321569 A) (@lem321568 A lt2 P)). Qed.
Lemma lem321571 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term433 A lt2 P) = (term434 A lt2 P)) = ((term432 A lt2 P) = (term447 A lt2 P)).
Proof. exact (MK_COMB (@lem321562 A lt2 P) (@lem321570 A lt2 P)). Qed.
Lemma lem321572 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term432 A lt2 P) = (term447 A lt2 P).
Proof. exact (EQ_MP (@lem321571 A lt2 P) (@lem321549 A lt2 P)). Qed.
Lemma lem321574 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem321575 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem321574 A P Q). Qed.
Lemma lem321576 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term448 A lt2 x P) = (term449 A lt2 x P).
Proof. exact (@lem321575 A (term427 A lt2 x P) (term365 A lt2 x P)). Qed.
Lemma lem321577 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term450 A lt2 x P z) = (term425 A lt2 x P z).
Proof. exact (eq_refl (term450 A lt2 x P z)). Qed.
Lemma lem321578 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term451 A lt2 x P) = (term427 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321577 A lt2 x P z)). Qed.
Lemma lem321579 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321580 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term452 A lt2 x P) = (term428 A lt2 x P).
Proof. exact (MK_COMB (@lem321579 A) (@lem321578 A lt2 x P)). Qed.
Lemma lem321581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321582 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term453 A lt2 x P) = (term442 A lt2 x P).
Proof. exact (MK_COMB (@lem321581) (@lem321580 A lt2 x P)). Qed.
Lemma lem321583 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term365 A lt2 x P) = (term365 A lt2 x P).
Proof. exact (eq_refl (term365 A lt2 x P)). Qed.
Lemma lem321584 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term448 A lt2 x P) = (term444 A lt2 x P).
Proof. exact (MK_COMB (@lem321582 A lt2 x P) (@lem321583 A lt2 x P)). Qed.
Lemma lem321585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321586 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term454 A lt2 x P) = (term455 A lt2 x P).
Proof. exact (MK_COMB (@lem321585) (@lem321584 A lt2 x P)). Qed.
Lemma lem321587 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term450 A lt2 x P z) = (term425 A lt2 x P z).
Proof. exact (eq_refl (term450 A lt2 x P z)). Qed.
Lemma lem321588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321589 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (z : A) : (term456 A lt2 x P z) = (term457 A lt2 x P z).
Proof. exact (MK_COMB (@lem321588) (@lem321587 A lt2 x P z)). Qed.
Lemma lem321590 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term365 A lt2 x P) = (term365 A lt2 x P).
Proof. exact (eq_refl (term365 A lt2 x P)). Qed.
Lemma lem321591 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term458 A z lt2 x P) = (term459 A z lt2 x P).
Proof. exact (MK_COMB (@lem321589 A lt2 x P z) (@lem321590 A lt2 x P)). Qed.
Lemma lem321592 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term460 A lt2 x P) = (term461 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321591 A z lt2 x P)). Qed.
Lemma lem321593 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321594 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term449 A lt2 x P) = (term462 A lt2 x P).
Proof. exact (MK_COMB (@lem321593 A) (@lem321592 A lt2 x P)). Qed.
Lemma lem321595 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term448 A lt2 x P) = (term449 A lt2 x P)) = ((term444 A lt2 x P) = (term462 A lt2 x P)).
Proof. exact (MK_COMB (@lem321586 A lt2 x P) (@lem321594 A lt2 x P)). Qed.
Lemma lem321596 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term444 A lt2 x P) = (term462 A lt2 x P).
Proof. exact (EQ_MP (@lem321595 A lt2 x P) (@lem321576 A lt2 x P)). Qed.
Lemma lem321597 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term446 A lt2 P) = (term463 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321596 A lt2 x P)). Qed.
Lemma lem321598 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321599 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term447 A lt2 P) = (term464 A lt2 P).
Proof. exact (MK_COMB (@lem321598 A) (@lem321597 A lt2 P)). Qed.
Lemma lem321600 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term432 A lt2 P) = (term464 A lt2 P).
Proof. exact (TRANS (@lem321572 A lt2 P) (@lem321599 A lt2 P)). Qed.
Lemma lem321601 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term404 A lt2 P) = (term464 A lt2 P).
Proof. exact (TRANS (@lem321545 A lt2 P) (@lem321600 A lt2 P)). Qed.
Lemma lem321602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321603 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term405 A lt2 P) = (term465 A lt2 P).
Proof. exact (MK_COMB (@lem321602) (@lem321601 A lt2 P)). Qed.
Lemma lem321604 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem321605 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term406 A lt2 P) = (term466 A lt2 P).
Proof. exact (MK_COMB (@lem321603 A lt2 P) (@lem321604 A P)). Qed.
Lemma lem321607 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem321608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem321607 A P Q). Qed.
Lemma lem321609 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term467 A lt2 P) = (term468 A lt2 P).
Proof. exact (@lem321608 A (term463 A lt2 P) (term72 A P)). Qed.
Lemma lem321610 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term469 A lt2 P x) = (term462 A lt2 x P).
Proof. exact (eq_refl (term469 A lt2 P x)). Qed.
Lemma lem321611 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term470 A lt2 P) = (term463 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321610 A lt2 x P)). Qed.
Lemma lem321612 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321613 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term471 A lt2 P) = (term464 A lt2 P).
Proof. exact (MK_COMB (@lem321612 A) (@lem321611 A lt2 P)). Qed.
Lemma lem321614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321615 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term472 A lt2 P) = (term465 A lt2 P).
Proof. exact (MK_COMB (@lem321614) (@lem321613 A lt2 P)). Qed.
Lemma lem321616 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem321617 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term467 A lt2 P) = (term466 A lt2 P).
Proof. exact (MK_COMB (@lem321615 A lt2 P) (@lem321616 A P)). Qed.
Lemma lem321618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321619 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term473 A lt2 P) = (term474 A lt2 P).
Proof. exact (MK_COMB (@lem321618) (@lem321617 A lt2 P)). Qed.
Lemma lem321620 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term469 A lt2 P x) = (term462 A lt2 x P).
Proof. exact (eq_refl (term469 A lt2 P x)). Qed.
Lemma lem321621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321622 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term475 A lt2 P x) = (term476 A lt2 x P).
Proof. exact (MK_COMB (@lem321621) (@lem321620 A lt2 x P)). Qed.
Lemma lem321623 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem321624 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term477 A lt2 x P) = (term478 A lt2 x P).
Proof. exact (MK_COMB (@lem321622 A lt2 x P) (@lem321623 A P)). Qed.
Lemma lem321625 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term479 A lt2 P) = (term480 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321624 A lt2 x P)). Qed.
Lemma lem321626 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321627 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term468 A lt2 P) = (term481 A lt2 P).
Proof. exact (MK_COMB (@lem321626 A) (@lem321625 A lt2 P)). Qed.
Lemma lem321628 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term467 A lt2 P) = (term468 A lt2 P)) = ((term466 A lt2 P) = (term481 A lt2 P)).
Proof. exact (MK_COMB (@lem321619 A lt2 P) (@lem321627 A lt2 P)). Qed.
Lemma lem321629 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term466 A lt2 P) = (term481 A lt2 P).
Proof. exact (EQ_MP (@lem321628 A lt2 P) (@lem321609 A lt2 P)). Qed.
Lemma lem321631 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem321632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem321631 A P Q). Qed.
Lemma lem321633 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term482 A lt2 x P) = (term483 A lt2 x P).
Proof. exact (@lem321632 A (term461 A lt2 x P) (term72 A P)). Qed.
Lemma lem321634 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term484 A lt2 x P z) = (term459 A z lt2 x P).
Proof. exact (eq_refl (term484 A lt2 x P z)). Qed.
Lemma lem321635 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term485 A lt2 x P) = (term461 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321634 A z lt2 x P)). Qed.
Lemma lem321636 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321637 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term486 A lt2 x P) = (term462 A lt2 x P).
Proof. exact (MK_COMB (@lem321636 A) (@lem321635 A lt2 x P)). Qed.
Lemma lem321638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321639 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term487 A lt2 x P) = (term476 A lt2 x P).
Proof. exact (MK_COMB (@lem321638) (@lem321637 A lt2 x P)). Qed.
Lemma lem321640 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem321641 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term482 A lt2 x P) = (term478 A lt2 x P).
Proof. exact (MK_COMB (@lem321639 A lt2 x P) (@lem321640 A P)). Qed.
Lemma lem321642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem321643 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term488 A lt2 x P) = (term489 A lt2 x P).
Proof. exact (MK_COMB (@lem321642) (@lem321641 A lt2 x P)). Qed.
Lemma lem321644 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term484 A lt2 x P z) = (term459 A z lt2 x P).
Proof. exact (eq_refl (term484 A lt2 x P z)). Qed.
Lemma lem321645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321646 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term490 A lt2 x P z) = (term491 A z lt2 x P).
Proof. exact (MK_COMB (@lem321645) (@lem321644 A z lt2 x P)). Qed.
Lemma lem321647 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (eq_refl (term72 A P)). Qed.
Lemma lem321648 {A : Type'} (z : A) (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term492 A lt2 x z P) = (term493 A z lt2 x P).
Proof. exact (MK_COMB (@lem321646 A z lt2 x P) (@lem321647 A P)). Qed.
Lemma lem321649 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term494 A lt2 x P) = (term495 A lt2 x P).
Proof. exact (fun_ext (fun z : A => @lem321648 A z lt2 x P)). Qed.
Lemma lem321650 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321651 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term483 A lt2 x P) = (term496 A lt2 x P).
Proof. exact (MK_COMB (@lem321650 A) (@lem321649 A lt2 x P)). Qed.
Lemma lem321652 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term482 A lt2 x P) = (term483 A lt2 x P)) = ((term478 A lt2 x P) = (term496 A lt2 x P)).
Proof. exact (MK_COMB (@lem321643 A lt2 x P) (@lem321651 A lt2 x P)). Qed.
Lemma lem321653 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term478 A lt2 x P) = (term496 A lt2 x P).
Proof. exact (EQ_MP (@lem321652 A lt2 x P) (@lem321633 A lt2 x P)). Qed.
Lemma lem321654 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term480 A lt2 P) = (term497 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem321653 A lt2 x P)). Qed.
Lemma lem321655 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem321656 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term481 A lt2 P) = (term498 A lt2 P).
Proof. exact (MK_COMB (@lem321655 A) (@lem321654 A lt2 P)). Qed.
Lemma lem321657 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term466 A lt2 P) = (term498 A lt2 P).
Proof. exact (TRANS (@lem321629 A lt2 P) (@lem321656 A lt2 P)). Qed.
Lemma lem321658 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term406 A lt2 P) = (term498 A lt2 P).
Proof. exact (TRANS (@lem321605 A lt2 P) (@lem321657 A lt2 P)). Qed.
Lemma lem321659 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term384 A lt2 P) = (term498 A lt2 P).
Proof. exact (TRANS (@lem321495 A lt2 P) (@lem321658 A lt2 P)). Qed.
Lemma lem321660 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term285 A lt2 P) = (term498 A lt2 P).
Proof. exact (TRANS (@lem321304 A lt2 P) (@lem321659 A lt2 P)). Qed.
Lemma lem321661 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term285 A lt2 P) : term498 A lt2 P.
Proof. exact (EQ_MP (@lem321660 A lt2 P) (@lem321062 A lt2 P h1)). Qed.
Lemma lem321667 {A : Type'} (P : A -> Prop) (x : A) (h1 : term153 A P x) : term153 A P x.
Proof. exact (h1). Qed.
Lemma lem321668 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term496 A lt2 x' P) : term496 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem321669 {A : Type'} (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term493 A z lt2 x' P) : term493 A z lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem321670 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term356 A lt2 y P.
Proof. exact (h1). Qed.
Lemma lem321676 {A : Type'} (P : A -> Prop) (x : A) (h1 : term153 A P x) : term153 A P x.
Proof. exact (h1). Qed.
Lemma lem321679 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem321680 {A : Type'} (P : A -> Prop) : (term284 A P) = (term284 A P).
Proof. exact (fun_ext (fun x : A => @lem321679 A P x)). Qed.
Lemma lem321681 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321682 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem321681 A) (@lem321680 A P)). Qed.
Lemma lem321695 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) : (term120 A lt2 x' P z) = (term120 A lt2 x' P z).
Proof. exact (eq_refl (term120 A lt2 x' P z)). Qed.
Lemma lem321696 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term130 A lt2 x' P) = (term130 A lt2 x' P).
Proof. exact (fun_ext (fun z : A => @lem321695 A lt2 x' P z)). Qed.
Lemma lem321697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321698 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term131 A lt2 x' P) = (term131 A lt2 x' P).
Proof. exact (MK_COMB (@lem321697 A) (@lem321696 A lt2 x' P)). Qed.
Lemma lem321703 {A : Type'} (P : A -> Prop) (x' : A) : (term106 A P x') = (term106 A P x').
Proof. exact (eq_refl (term106 A P x')). Qed.
Lemma lem321704 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term363 A lt2 x' P) = (term363 A lt2 x' P).
Proof. exact (MK_COMB (@lem321703 A P x') (@lem321698 A lt2 x' P)). Qed.
Lemma lem321711 {A : Type'} (P : A -> Prop) (x' : A) : (term132 A P x') = (term132 A P x').
Proof. exact (eq_refl (term132 A P x')). Qed.
Lemma lem321712 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term365 A lt2 x' P) = (term365 A lt2 x' P).
Proof. exact (MK_COMB (@lem321711 A P x') (@lem321704 A lt2 x' P)). Qed.
Lemma lem321741 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) : (term457 A lt2 x' P z) = (term457 A lt2 x' P z).
Proof. exact (eq_refl (term457 A lt2 x' P z)). Qed.
Lemma lem321742 {A : Type'} (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term459 A z lt2 x' P) = (term459 A z lt2 x' P).
Proof. exact (MK_COMB (@lem321741 A lt2 x' P z) (@lem321712 A lt2 x' P)). Qed.
Lemma lem321743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem321744 {A : Type'} (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term491 A z lt2 x' P) = (term491 A z lt2 x' P).
Proof. exact (MK_COMB (@lem321743) (@lem321742 A z lt2 x' P)). Qed.
Lemma lem321745 {A : Type'} (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term493 A z lt2 x' P) = (term493 A z lt2 x' P).
Proof. exact (MK_COMB (@lem321744 A z lt2 x' P) (@lem321682 A P)). Qed.
Lemma lem321746 {A : Type'} (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term493 A z lt2 x' P) : term493 A z lt2 x' P.
Proof. exact (EQ_MP (@lem321745 A z lt2 x' P) (@lem321669 A z lt2 x' P h1)). Qed.
Lemma lem321769 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term352 A lt2 y P x) = (term352 A lt2 y P x).
Proof. exact (eq_refl (term352 A lt2 y P x)). Qed.
Lemma lem321770 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term354 A lt2 y P) = (term354 A lt2 y P).
Proof. exact (fun_ext (fun x : A => @lem321769 A lt2 y P x)). Qed.
Lemma lem321771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321772 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term356 A lt2 y P) = (term356 A lt2 y P).
Proof. exact (MK_COMB (@lem321771 A) (@lem321770 A lt2 y P)). Qed.
Lemma lem321773 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term356 A lt2 y P.
Proof. exact (EQ_MP (@lem321772 A lt2 y P) (@lem321670 A lt2 y P h1)). Qed.
Lemma lem321774 {A : Type'} (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term459 A z lt2 x' P) : term459 A z lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem321775 {A : Type'} (P : A -> Prop) (h1 : term72 A P) : term72 A P.
Proof. exact (h1). Qed.
Lemma lem321776 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : term425 A lt2 x' P z.
Proof. exact (h1). Qed.
Lemma lem321777 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term365 A lt2 x' P) : term365 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem321778 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : term412 A lt2 x' P z.
Proof. exact (proj2 (@lem321776 A lt2 x' P z h1)). Qed.
Lemma lem321784 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term365 A lt2 x' P) : term363 A lt2 x' P.
Proof. exact (proj2 (@lem321777 A lt2 x' P h1)). Qed.
Lemma lem321787 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term131 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem321865 {A : Type'} (P : A -> Prop) (x' : A) (h1 : P x') : P x'.
Proof. exact (h1). Qed.
Lemma lem321887 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term352 A lt2 y P x) = (term499 A lt2 y P x).
Proof. exact (@lem19699 (term500 A lt2 y x) (term501 A P y x) (P x)). Qed.
Lemma lem321888 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term354 A lt2 y P) = (term502 A lt2 y P).
Proof. exact (fun_ext (fun x : A => @lem321887 A lt2 y P x)). Qed.
Lemma lem321889 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321891 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term356 A lt2 y P) = (term503 A lt2 y P).
Proof. exact (MK_COMB (@lem321889 A) (@lem321888 A lt2 y P)). Qed.
Lemma lem321892 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term503 A lt2 y P.
Proof. exact (EQ_MP (@lem321891 A lt2 y P) (@lem321773 A lt2 y P h1)). Qed.
Lemma lem321904 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) : (term120 A lt2 x' P z) = (term120 A lt2 x' P z).
Proof. exact (eq_refl (term120 A lt2 x' P z)). Qed.
Lemma lem321905 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term130 A lt2 x' P) = (term130 A lt2 x' P).
Proof. exact (fun_ext (fun z : A => @lem321904 A lt2 x' P z)). Qed.
Lemma lem321906 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321908 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term131 A lt2 x' P) = (term131 A lt2 x' P).
Proof. exact (MK_COMB (@lem321906 A) (@lem321905 A lt2 x' P)). Qed.
Lemma lem321909 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term131 A lt2 x' P.
Proof. exact (EQ_MP (@lem321908 A lt2 x' P) (@lem321787 A lt2 x' P h1)). Qed.
Lemma lem321913 {A : Type'} (P : A -> Prop) (x : A) (h1 : term153 A P x) : term153 A P x.
Proof. exact (h1). Qed.
Lemma lem321938 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem321939 {A : Type'} (P : A -> Prop) : (term284 A P) = (term284 A P).
Proof. exact (fun_ext (fun x : A => @lem321938 A P x)). Qed.
Lemma lem321940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem321942 {A : Type'} (P : A -> Prop) : (term72 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem321940 A) (@lem321939 A P)). Qed.
Lemma lem321943 {A : Type'} (P : A -> Prop) (h1 : term72 A P) : term72 A P.
Proof. exact (EQ_MP (@lem321942 A P) (@lem321775 A P h1)). Qed.
Lemma lem321950 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term504 A lt2 y P _7007.
Proof. exact (@lem321892 A lt2 y P h1 _7007). Qed.
Lemma lem321951 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_7007 : A) : (term504 A lt2 y P _7007) = (term499 A lt2 y P _7007).
Proof. exact (eq_refl (term504 A lt2 y P _7007)). Qed.
Lemma lem321952 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term499 A lt2 y P _7007.
Proof. exact (EQ_MP (@lem321951 A lt2 y P _7007) (@lem321950 A _7007 lt2 y P h1)). Qed.
Lemma lem321953 {A : Type'} (_7008 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term222 A lt2 x' P _7008.
Proof. exact (@lem321909 A lt2 x' P h1 _7008). Qed.
Lemma lem321954 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_7008 : A) : (term222 A lt2 x' P _7008) = (term120 A lt2 x' P _7008).
Proof. exact (eq_refl (term222 A lt2 x' P _7008)). Qed.
Lemma lem321959 {A : Type'} (_7010 : A) (P : A -> Prop) (h1 : term72 A P) : term23 A P _7010.
Proof. exact (@lem321943 A P h1 _7010). Qed.
Lemma lem321960 {A : Type'} (P : A -> Prop) (_7010 : A) : (term23 A P _7010) = (P _7010).
Proof. exact (eq_refl (term23 A P _7010)). Qed.
Lemma lem321975 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : term153 A P x'.
Proof. exact (proj1 (@lem321778 A lt2 x' P z h1)). Qed.
Lemma lem321995 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term365 A lt2 x' P) : term153 A P x'.
Proof. exact (proj1 (@lem321777 A lt2 x' P h1)). Qed.
Lemma lem321997 {A : Type'} (P : A -> Prop) (x' : A) (h1 : P x') : P x'.
Proof. exact (h1). Qed.
Lemma lem322013 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term365 A lt2 x' P) : term153 A P x'.
Proof. exact (proj1 (@lem321777 A lt2 x' P h1)). Qed.
Lemma lem322019 {A : Type'} (_7008 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term120 A lt2 x' P _7008.
Proof. exact (EQ_MP (@lem321954 A lt2 x' P _7008) (@lem321953 A _7008 lt2 x' P h1)). Qed.
Lemma lem322025 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term505 A lt2 y P _7007.
Proof. exact (proj1 (@lem321952 A _7007 lt2 y P h1)). Qed.
Lemma lem322031 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term506 A y P _7007.
Proof. exact (proj2 (@lem321952 A _7007 lt2 y P h1)). Qed.
Lemma lem322033 {A : Type'} (P : A -> Prop) (x : A) (h1 : term153 A P x) : term153 A P x.
Proof. exact (h1). Qed.
Lemma lem322049 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : P x'.
Proof. exact (proj1 (@lem321776 A lt2 x' P z h1)). Qed.
Lemma lem322050 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : term225 A P x'.
Proof. exact (fun h0 : term153 A P x' => @lem322049 A lt2 x' P z h1). Qed.
Lemma lem322052 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322053 {A : Type'} (P : A -> Prop) (x' : A) : (term225 A P x') = (P x').
Proof. exact (@lem322052 (P x')). Qed.
Lemma lem322054 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : P x'.
Proof. exact (EQ_MP (@lem322053 A P x') (@lem322050 A lt2 x' P z h1)). Qed.
Lemma lem322057 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem322059 {A : Type'} (P : A -> Prop) (x' : A) : (term153 A P x') = (term227 A P x').
Proof. exact (@lem322057 (P x')). Qed.
Lemma lem322062 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : term227 A P x'.
Proof. exact (EQ_MP (@lem322059 A P x') (@lem321975 A lt2 x' P z h1)). Qed.
Lemma lem322065 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : False.
Proof. exact (@lem322062 A lt2 x' P z h1 (@lem322054 A lt2 x' P z h1)). Qed.
Lemma lem322066 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : term228.
Proof. exact (fun h0 : ~ False => @lem322065 A lt2 x' P z h1). Qed.
Lemma lem322068 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322069 : term228 = False.
Proof. exact (@lem322068 False). Qed.
Lemma lem322070 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (z : A) (h1 : term425 A lt2 x' P z) : False.
Proof. exact (EQ_MP (@lem322069) (@lem322066 A lt2 x' P z h1)). Qed.
Lemma lem322072 {A : Type'} (P : A -> Prop) (x' : A) (h1 : P x') : P x'.
Proof. exact (h1). Qed.
Lemma lem322073 {A : Type'} (P : A -> Prop) (x' : A) (h1 : P x') : term225 A P x'.
Proof. exact (fun h0 : term153 A P x' => @lem322072 A P x' h1). Qed.
Lemma lem322075 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322076 {A : Type'} (P : A -> Prop) (x' : A) : (term225 A P x') = (P x').
Proof. exact (@lem322075 (P x')). Qed.
Lemma lem322077 {A : Type'} (P : A -> Prop) (x' : A) (h1 : P x') : P x'.
Proof. exact (EQ_MP (@lem322076 A P x') (@lem322073 A P x' h1)). Qed.
Lemma lem322080 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem322082 {A : Type'} (P : A -> Prop) (x' : A) : (term153 A P x') = (term227 A P x').
Proof. exact (@lem322080 (P x')). Qed.
Lemma lem322085 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term365 A lt2 x' P) : term227 A P x'.
Proof. exact (EQ_MP (@lem322082 A P x') (@lem321995 A lt2 x' P h1)). Qed.
Lemma lem322088 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : False.
Proof. exact (@lem322085 A lt2 x' P h2 (@lem322077 A P x' h1)). Qed.
Lemma lem322089 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : term228.
Proof. exact (fun h0 : ~ False => @lem322088 A lt2 x' P h1 h2). Qed.
Lemma lem322091 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322092 : term228 = False.
Proof. exact (@lem322091 False). Qed.
Lemma lem322093 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322092) (@lem322089 A lt2 x' P h1 h2)). Qed.
Lemma lem322096 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term153 A P x') : term153 A P x'.
Proof. exact (h1). Qed.
Lemma lem322097 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term153 A P x') : term507 A P x'.
Proof. exact (fun h0 : P x' => @lem322096 A P x' h1). Qed.
Lemma lem322099 (p : Prop) : (term508 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem322100 {A : Type'} (P : A -> Prop) (x' : A) : (term507 A P x') = (term153 A P x').
Proof. exact (@lem322099 (P x')). Qed.
Lemma lem322101 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term153 A P x') : term153 A P x'.
Proof. exact (EQ_MP (@lem322100 A P x') (@lem322097 A P x' h1)). Qed.
Lemma lem322103 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem322106 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_7007 : A) : (term505 A lt2 y P _7007) = (term509 A P lt2 y _7007).
Proof. exact (@lem322103 (P _7007) (term500 A lt2 y _7007)). Qed.
Lemma lem322109 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term509 A P lt2 y _7007.
Proof. exact (EQ_MP (@lem322106 A P lt2 y _7007) (@lem322025 A _7007 lt2 y P h1)). Qed.
Lemma lem322110 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term509 A P lt2 y _7007.
Proof. exact (@lem322109 A _7007 lt2 y P h1). Qed.
Lemma lem322111 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term509 A P lt2 y x'.
Proof. exact (@lem322110 A x' lt2 y P h1). Qed.
Lemma lem322114 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term356 A lt2 y P) (h2 : term153 A P x') : term500 A lt2 y x'.
Proof. exact (@lem322111 A x' lt2 y P h1 (@lem322101 A P x' h2)). Qed.
Lemma lem322115 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term356 A lt2 y P) (h2 : term153 A P x') : term510 A lt2 y x'.
Proof. exact (fun h0 : term511 A lt2 y x' => @lem322114 A lt2 y P x' h1 h2). Qed.
Lemma lem322117 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322118 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x' : A) : (term510 A lt2 y x') = (term500 A lt2 y x').
Proof. exact (@lem322117 (term500 A lt2 y x')). Qed.
Lemma lem322119 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term356 A lt2 y P) (h2 : term153 A P x') : term500 A lt2 y x'.
Proof. exact (EQ_MP (@lem322118 A lt2 y x') (@lem322115 A lt2 y P x' h1 h2)). Qed.
Lemma lem322125 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem322126 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : (term120 A lt2 x' P _7008) = (term230 A P lt2 _7008 x').
Proof. exact (@lem322125 (P _7008) (term217 A lt2 _7008 x')). Qed.
Lemma lem322132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem322133 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : (term231 A lt2 x' P _7008) = (term232 A P lt2 _7008 x').
Proof. exact (MK_COMB (@lem322132) (@lem322126 A P lt2 _7008 x')). Qed.
Lemma lem322139 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : (term230 A P lt2 _7008 x') = (term230 A P lt2 _7008 x').
Proof. exact (eq_refl (term230 A P lt2 _7008 x')). Qed.
Lemma lem322140 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : ((term120 A lt2 x' P _7008) = (term230 A P lt2 _7008 x')) = ((term230 A P lt2 _7008 x') = (term230 A P lt2 _7008 x')).
Proof. exact (MK_COMB (@lem322133 A P lt2 _7008 x') (@lem322139 A P lt2 _7008 x')). Qed.
Lemma lem322142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem322143 (x : Prop) : (x = x) = True.
Proof. exact (@lem322142 Prop x). Qed.
Lemma lem322144 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : ((term230 A P lt2 _7008 x') = (term230 A P lt2 _7008 x')) = True.
Proof. exact (@lem322143 (term230 A P lt2 _7008 x')). Qed.
Lemma lem322145 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : ((term120 A lt2 x' P _7008) = (term230 A P lt2 _7008 x')) = True.
Proof. exact (TRANS (@lem322140 A P lt2 _7008 x') (@lem322144 A P lt2 _7008 x')). Qed.
Lemma lem322146 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : True = ((term120 A lt2 x' P _7008) = (term230 A P lt2 _7008 x')).
Proof. exact (SYM (@lem322145 A P lt2 _7008 x')). Qed.
Lemma lem322147 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_7008 : A) (x' : A) : (term120 A lt2 x' P _7008) = (term230 A P lt2 _7008 x').
Proof. exact (EQ_MP (@lem322146 A P lt2 _7008 x') (@lem0)). Qed.
Lemma lem322148 {A : Type'} (_7008 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term230 A P lt2 _7008 x'.
Proof. exact (EQ_MP (@lem322147 A P lt2 _7008 x') (@lem322019 A _7008 lt2 x' P h1)). Qed.
Lemma lem322150 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem322151 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_7008 : A) : (term230 A P lt2 _7008 x') = (term234 A lt2 x' P _7008).
Proof. exact (@lem322150 (term217 A lt2 _7008 x') (P _7008)). Qed.
Lemma lem322153 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem322154 {A : Type'} (lt2 : type1402 A) (_7008 : A) (x' : A) : (term235 A lt2 _7008 x') = (lt2 _7008 x').
Proof. exact (@lem322153 (lt2 _7008 x')). Qed.
Lemma lem322155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322156 {A : Type'} (lt2 : type1402 A) (_7008 : A) (x' : A) : (term236 A lt2 _7008 x') = (term237 A lt2 _7008 x').
Proof. exact (MK_COMB (@lem322155) (@lem322154 A lt2 _7008 x')). Qed.
Lemma lem322157 {A : Type'} (P : A -> Prop) (_7008 : A) : (P _7008) = (P _7008).
Proof. exact (eq_refl (P _7008)). Qed.
Lemma lem322158 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_7008 : A) : (term234 A lt2 x' P _7008) = (term103 A lt2 x' P _7008).
Proof. exact (MK_COMB (@lem322156 A lt2 _7008 x') (@lem322157 A P _7008)). Qed.
Lemma lem322159 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_7008 : A) : (term230 A P lt2 _7008 x') = (term103 A lt2 x' P _7008).
Proof. exact (TRANS (@lem322151 A lt2 x' P _7008) (@lem322158 A lt2 x' P _7008)). Qed.
Lemma lem322162 {A : Type'} (_7008 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term103 A lt2 x' P _7008.
Proof. exact (EQ_MP (@lem322159 A lt2 x' P _7008) (@lem322148 A _7008 lt2 x' P h1)). Qed.
Lemma lem322163 {A : Type'} (_7008 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term103 A lt2 x' P _7008.
Proof. exact (@lem322162 A _7008 lt2 x' P h1). Qed.
Lemma lem322164 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) : term512 A lt2 P y x'.
Proof. exact (@lem322163 A (y x') lt2 x' P h1). Qed.
Lemma lem322167 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term153 A P x') : term513 A P y x'.
Proof. exact (@lem322164 A y lt2 x' P h1 (@lem322119 A lt2 y P x' h2 h3)). Qed.
Lemma lem322168 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term153 A P x') : term514 A P y x'.
Proof. exact (fun h0 : term501 A P y x' => @lem322167 A lt2 y P x' h1 h2 h3). Qed.
Lemma lem322170 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322171 {A : Type'} (P : A -> Prop) (y : A -> A) (x' : A) : (term514 A P y x') = (term513 A P y x').
Proof. exact (@lem322170 (term513 A P y x')). Qed.
Lemma lem322172 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term153 A P x') : term513 A P y x'.
Proof. exact (EQ_MP (@lem322171 A P y x') (@lem322168 A lt2 y P x' h1 h2 h3)). Qed.
Lemma lem322178 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem322179 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : (term506 A y P _7007) = (term515 A P y _7007).
Proof. exact (@lem322178 (P _7007) (term501 A P y _7007)). Qed.
Lemma lem322185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem322186 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : (term516 A y P _7007) = (term517 A P y _7007).
Proof. exact (MK_COMB (@lem322185) (@lem322179 A P y _7007)). Qed.
Lemma lem322192 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : (term515 A P y _7007) = (term515 A P y _7007).
Proof. exact (eq_refl (term515 A P y _7007)). Qed.
Lemma lem322193 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : ((term506 A y P _7007) = (term515 A P y _7007)) = ((term515 A P y _7007) = (term515 A P y _7007)).
Proof. exact (MK_COMB (@lem322186 A P y _7007) (@lem322192 A P y _7007)). Qed.
Lemma lem322195 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem322196 (x : Prop) : (x = x) = True.
Proof. exact (@lem322195 Prop x). Qed.
Lemma lem322197 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : ((term515 A P y _7007) = (term515 A P y _7007)) = True.
Proof. exact (@lem322196 (term515 A P y _7007)). Qed.
Lemma lem322198 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : ((term506 A y P _7007) = (term515 A P y _7007)) = True.
Proof. exact (TRANS (@lem322193 A P y _7007) (@lem322197 A P y _7007)). Qed.
Lemma lem322199 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : True = ((term506 A y P _7007) = (term515 A P y _7007)).
Proof. exact (SYM (@lem322198 A P y _7007)). Qed.
Lemma lem322200 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : (term506 A y P _7007) = (term515 A P y _7007).
Proof. exact (EQ_MP (@lem322199 A P y _7007) (@lem0)). Qed.
Lemma lem322201 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term515 A P y _7007.
Proof. exact (EQ_MP (@lem322200 A P y _7007) (@lem322031 A _7007 lt2 y P h1)). Qed.
Lemma lem322203 (b : Prop) (a : Prop) : (a \/ b) = (term233 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem322204 {A : Type'} (y : A -> A) (P : A -> Prop) (_7007 : A) : (term515 A P y _7007) = (term518 A y P _7007).
Proof. exact (@lem322203 (term501 A P y _7007) (P _7007)). Qed.
Lemma lem322206 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem322207 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : (term519 A P y _7007) = (term513 A P y _7007).
Proof. exact (@lem322206 (term513 A P y _7007)). Qed.
Lemma lem322208 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322209 {A : Type'} (P : A -> Prop) (y : A -> A) (_7007 : A) : (term520 A P y _7007) = (term521 A P y _7007).
Proof. exact (MK_COMB (@lem322208) (@lem322207 A P y _7007)). Qed.
Lemma lem322210 {A : Type'} (P : A -> Prop) (_7007 : A) : (P _7007) = (P _7007).
Proof. exact (eq_refl (P _7007)). Qed.
Lemma lem322211 {A : Type'} (y : A -> A) (P : A -> Prop) (_7007 : A) : (term518 A y P _7007) = (term522 A y P _7007).
Proof. exact (MK_COMB (@lem322209 A P y _7007) (@lem322210 A P _7007)). Qed.
Lemma lem322212 {A : Type'} (y : A -> A) (P : A -> Prop) (_7007 : A) : (term515 A P y _7007) = (term522 A y P _7007).
Proof. exact (TRANS (@lem322204 A y P _7007) (@lem322211 A y P _7007)). Qed.
Lemma lem322215 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term522 A y P _7007.
Proof. exact (EQ_MP (@lem322212 A y P _7007) (@lem322201 A _7007 lt2 y P h1)). Qed.
Lemma lem322216 {A : Type'} (_7007 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term522 A y P _7007.
Proof. exact (@lem322215 A _7007 lt2 y P h1). Qed.
Lemma lem322217 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term356 A lt2 y P) : term522 A y P x'.
Proof. exact (@lem322216 A x' lt2 y P h1). Qed.
Lemma lem322220 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term153 A P x') : P x'.
Proof. exact (@lem322217 A x' lt2 y P h2 (@lem322172 A lt2 y P x' h1 h2 h3)). Qed.
Lemma lem322221 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) : term225 A P x'.
Proof. exact (fun h0 : term153 A P x' => @lem322220 A lt2 y P x' h1 h2 h0). Qed.
Lemma lem322223 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322224 {A : Type'} (P : A -> Prop) (x' : A) : (term225 A P x') = (P x').
Proof. exact (@lem322223 (P x')). Qed.
Lemma lem322225 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) : P x'.
Proof. exact (EQ_MP (@lem322224 A P x') (@lem322221 A x' lt2 y P h1 h2)). Qed.
Lemma lem322228 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem322230 {A : Type'} (P : A -> Prop) (x' : A) : (term153 A P x') = (term227 A P x').
Proof. exact (@lem322228 (P x')). Qed.
Lemma lem322233 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term365 A lt2 x' P) : term227 A P x'.
Proof. exact (EQ_MP (@lem322230 A P x') (@lem322013 A lt2 x' P h1)). Qed.
Lemma lem322236 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term365 A lt2 x' P) : False.
Proof. exact (@lem322233 A lt2 x' P h3 (@lem322225 A x' lt2 y P h1 h2)). Qed.
Lemma lem322237 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term365 A lt2 x' P) : term228.
Proof. exact (fun h0 : ~ False => @lem322236 A y lt2 x' P h1 h2 h3). Qed.
Lemma lem322239 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322240 : term228 = False.
Proof. exact (@lem322239 False). Qed.
Lemma lem322241 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term365 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322240) (@lem322237 A y lt2 x' P h1 h2 h3)). Qed.
Lemma lem322243 {A : Type'} (_7010 : A) (P : A -> Prop) (h1 : term72 A P) : P _7010.
Proof. exact (EQ_MP (@lem321960 A P _7010) (@lem321959 A _7010 P h1)). Qed.
Lemma lem322244 {A : Type'} (_7010 : A) (P : A -> Prop) (h1 : term72 A P) : P _7010.
Proof. exact (@lem322243 A _7010 P h1). Qed.
Lemma lem322245 {A : Type'} (x : A) (P : A -> Prop) (h1 : term72 A P) : P x.
Proof. exact (@lem322244 A x P h1). Qed.
Lemma lem322246 {A : Type'} (x : A) (P : A -> Prop) (h1 : term72 A P) : term225 A P x.
Proof. exact (fun h0 : term153 A P x => @lem322245 A x P h1). Qed.
Lemma lem322248 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322249 {A : Type'} (P : A -> Prop) (x : A) : (term225 A P x) = (P x).
Proof. exact (@lem322248 (P x)). Qed.
Lemma lem322250 {A : Type'} (x : A) (P : A -> Prop) (h1 : term72 A P) : P x.
Proof. exact (EQ_MP (@lem322249 A P x) (@lem322246 A x P h1)). Qed.
Lemma lem322253 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem322255 {A : Type'} (P : A -> Prop) (x : A) : (term153 A P x) = (term227 A P x).
Proof. exact (@lem322253 (P x)). Qed.
Lemma lem322258 {A : Type'} (P : A -> Prop) (x : A) (h1 : term153 A P x) : term227 A P x.
Proof. exact (EQ_MP (@lem322255 A P x) (@lem322033 A P x h1)). Qed.
Lemma lem322261 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : False.
Proof. exact (@lem322258 A P x h2 (@lem322250 A x P h1)). Qed.
Lemma lem322262 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : term228.
Proof. exact (fun h0 : ~ False => @lem322261 A P x h1 h2). Qed.
Lemma lem322264 (p : Prop) : (term226 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem322265 : term228 = False.
Proof. exact (@lem322264 False). Qed.
Lemma lem322266 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : False.
Proof. exact (EQ_MP (@lem322265) (@lem322262 A P x h1 h2)). Qed.
Lemma lem322267 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : (term153 A P x) = False.
Proof. exact (prop_ext (fun h3 : term153 A P x => @lem322266 A P x h1 h2) (fun h3 : False => @lem322033 A P x h2)). Qed.
Lemma lem322268 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : False.
Proof. exact (EQ_MP (@lem322267 A P x h1 h2) (@lem322033 A P x h2)). Qed.
Lemma lem322269 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : (P x') = False.
Proof. exact (prop_ext (fun h3 : P x' => @lem322093 A lt2 x' P h1 h2) (fun h3 : False => @lem321997 A P x' h1)). Qed.
Lemma lem322270 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322269 A lt2 x' P h1 h2) (@lem321997 A P x' h1)). Qed.
Lemma lem322271 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : (term153 A P x) = False.
Proof. exact (prop_ext (fun h3 : term153 A P x => @lem322268 A P x h1 h2) (fun h3 : False => @lem321913 A P x h2)). Qed.
Lemma lem322272 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : False.
Proof. exact (EQ_MP (@lem322271 A P x h1 h2) (@lem321913 A P x h2)). Qed.
Lemma lem322273 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : (P x') = False.
Proof. exact (prop_ext (fun h3 : P x' => @lem322270 A lt2 x' P h1 h2) (fun h3 : False => @lem321865 A P x' h1)). Qed.
Lemma lem322274 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322273 A lt2 x' P h1 h2) (@lem321865 A P x' h1)). Qed.
Lemma lem322275 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : (term72 A P) = False.
Proof. exact (prop_ext (fun h3 : term72 A P => @lem322272 A P x h1 h2) (fun h3 : False => @lem321943 A P h1)). Qed.
Lemma lem322276 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : False.
Proof. exact (EQ_MP (@lem322275 A P x h1 h2) (@lem321943 A P h1)). Qed.
Lemma lem322277 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : (term153 A P x) = False.
Proof. exact (prop_ext (fun h3 : term153 A P x => @lem322276 A P x h1 h2) (fun h3 : False => @lem321913 A P x h2)). Qed.
Lemma lem322278 {A : Type'} (P : A -> Prop) (x : A) (h1 : term72 A P) (h2 : term153 A P x) : False.
Proof. exact (EQ_MP (@lem322277 A P x h1 h2) (@lem321913 A P x h2)). Qed.
Lemma lem322279 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term365 A lt2 x' P) : (term131 A lt2 x' P) = False.
Proof. exact (prop_ext (fun h4 : term131 A lt2 x' P => @lem322241 A y lt2 x' P h1 h2 h3) (fun h4 : False => @lem321909 A lt2 x' P h1)). Qed.
Lemma lem322280 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term131 A lt2 x' P) (h2 : term356 A lt2 y P) (h3 : term365 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322279 A y lt2 x' P h1 h2 h3) (@lem321909 A lt2 x' P h1)). Qed.
Lemma lem322281 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : (P x') = False.
Proof. exact (prop_ext (fun h3 : P x' => @lem322274 A lt2 x' P h1 h2) (fun h3 : False => @lem321865 A P x' h1)). Qed.
Lemma lem322282 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : P x') (h2 : term365 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322281 A lt2 x' P h1 h2) (@lem321865 A P x' h1)). Qed.
Lemma lem322283 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term365 A lt2 x' P) : False.
Proof. exact (or_elim (@lem321784 A lt2 x' P h2) (fun h0 : P x' => @lem322282 A lt2 x' P h0 h2) (fun h0 : term131 A lt2 x' P => @lem322280 A y lt2 x' P h0 h1 h2)). Qed.
Lemma lem322284 {A : Type'} (y : A -> A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term459 A z lt2 x' P) : False.
Proof. exact (or_elim (@lem321774 A z lt2 x' P h2) (fun h0 : term425 A lt2 x' P z => @lem322070 A lt2 x' P z h0) (fun h0 : term365 A lt2 x' P => @lem322283 A y lt2 x' P h1 h0)). Qed.
Lemma lem322285 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : False.
Proof. exact (or_elim (@lem321746 A z lt2 x' P h3) (fun h0 : term459 A z lt2 x' P => @lem322284 A y z lt2 x' P h1 h0) (fun h0 : term72 A P => @lem322278 A P x h0 h2)). Qed.
Lemma lem322286 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : (term356 A lt2 y P) = False.
Proof. exact (prop_ext (fun h4 : term356 A lt2 y P => @lem322285 A y x z lt2 x' P h1 h2 h3) (fun h4 : False => @lem321773 A lt2 y P h1)). Qed.
Lemma lem322287 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322286 A y x z lt2 x' P h1 h2 h3) (@lem321773 A lt2 y P h1)). Qed.
Lemma lem322288 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : (term493 A z lt2 x' P) = False.
Proof. exact (prop_ext (fun h4 : term493 A z lt2 x' P => @lem322287 A y x z lt2 x' P h1 h2 h3) (fun h4 : False => @lem321746 A z lt2 x' P h3)). Qed.
Lemma lem322289 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322288 A y x z lt2 x' P h1 h2 h3) (@lem321746 A z lt2 x' P h3)). Qed.
Lemma lem322290 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : (term153 A P x) = False.
Proof. exact (prop_ext (fun h4 : term153 A P x => @lem322289 A y x z lt2 x' P h1 h2 h3) (fun h4 : False => @lem321676 A P x h2)). Qed.
Lemma lem322291 {A : Type'} (y : A -> A) (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term356 A lt2 y P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : False.
Proof. exact (EQ_MP (@lem322290 A y x z lt2 x' P h1 h2 h3) (@lem321676 A P x h2)). Qed.
Lemma lem322292 {A : Type'} (x : A) (z : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term153 A P x) (h3 : term493 A z lt2 x' P) : False.
Proof. exact (ex_elim (@lem321235 A lt2 P h1) (fun y : A -> A => fun h0 : term358 A lt2 P y => @lem322291 A y x z lt2 x' P h0 h2 h3)). Qed.
Lemma lem322293 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (x : A) (h1 : term9 A lt2 P) (h2 : term496 A lt2 x' P) (h3 : term153 A P x) : False.
Proof. exact (ex_elim (@lem321668 A lt2 x' P h2) (fun z : A => fun h0 : term495 A lt2 x' P z => @lem322292 A x z lt2 x' P h1 h3 h0)). Qed.
Lemma lem322294 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term153 A P x) (h3 : term285 A lt2 P) : False.
Proof. exact (ex_elim (@lem321661 A lt2 P h3) (fun x' : A => fun h0 : term497 A lt2 P x' => @lem322293 A lt2 x' P x h1 h0 h2)). Qed.
Lemma lem322295 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term153 A P x) (h3 : term285 A lt2 P) : (term153 A P x) = False.
Proof. exact (prop_ext (fun h4 : term153 A P x => @lem322294 A x lt2 P h1 h2 h3) (fun h4 : False => @lem321667 A P x h2)). Qed.
Lemma lem322296 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term153 A P x) (h3 : term285 A lt2 P) : False.
Proof. exact (EQ_MP (@lem322295 A x lt2 P h1 h2 h3) (@lem321667 A P x h2)). Qed.
Lemma lem322297 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term153 A P x) (h3 : term285 A lt2 P) : (term153 A P x) = False.
Proof. exact (prop_ext (fun h4 : term153 A P x => @lem322296 A x lt2 P h1 h2 h3) (fun h4 : False => @lem321067 A P x h2)). Qed.
Lemma lem322298 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term153 A P x) (h3 : term285 A lt2 P) : False.
Proof. exact (EQ_MP (@lem322297 A x lt2 P h1 h2 h3) (@lem321067 A P x h2)). Qed.
Lemma lem322299 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term285 A lt2 P) : term312 A P x.
Proof. exact (fun h0 : term153 A P x => @lem322298 A x lt2 P h1 h0 h2). Qed.
Lemma lem322300 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term285 A lt2 P) : P x.
Proof. exact (EQ_MP (@lem321066 A P x) (@lem322299 A x lt2 P h1 h2)). Qed.
Lemma lem322305 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term285 A lt2 P) : term72 A P.
Proof. exact (fun x : A => @lem322300 A x lt2 P h1 h2). Qed.
Lemma lem322306 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term289 A lt2 P.
Proof. exact (fun h0 : term285 A lt2 P => @lem322305 A lt2 P h1 h0). Qed.
Lemma lem322307 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term298 A lt2 P.
Proof. exact (fun h0 : term9 A lt2 P => @lem322306 A lt2 P h0). Qed.
Lemma lem322312 {A : Type'} (P : A -> Prop) : term302 A P.
Proof. exact (fun lt2 : type1402 A => @lem322307 A lt2 P). Qed.
Lemma lem322317 {A : Type'} : term306 A.
Proof. exact (fun P : A -> Prop => @lem322312 A P). Qed.
Lemma lem322318 {A : Type'} : term305 A.
Proof. exact (EQ_MP (@lem321060 A) (@lem322317 A)). Qed.
Lemma lem322319 {A : Type'} (P : A -> Prop) : term523 A P.
Proof. exact (@lem322318 A P). Qed.
Lemma lem322320 {A : Type'} (P : A -> Prop) : (term523 A P) = (term301 A P).
Proof. exact (eq_refl (term523 A P)). Qed.
Lemma lem322321 {A : Type'} (P : A -> Prop) : term301 A P.
Proof. exact (EQ_MP (@lem322320 A P) (@lem322319 A P)). Qed.
Lemma lem322322 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term524 A P lt2.
Proof. exact (@lem322321 A P lt2). Qed.
Lemma lem322323 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term524 A P lt2) = (term292 A lt2 P).
Proof. exact (eq_refl (term524 A P lt2)). Qed.
Lemma lem322324 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term292 A lt2 P.
Proof. exact (EQ_MP (@lem322323 A lt2 P) (@lem322322 A P lt2)). Qed.
Lemma lem322326 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term292 A lt2 P.
Proof. exact (@lem320862 A lt2 P (@lem322324 A lt2 P)). Qed.
Lemma lem322327 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term290 A lt2 P.
Proof. exact (@lem322326 A lt2 P (@lem318511 A lt2 P h1)). Qed.
Lemma lem322328 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term291 A lt2 P) : False.
Proof. exact (@lem322327 A lt2 P h1 (@lem320846 A lt2 P h2)). Qed.
Lemma lem322329 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term291 A lt2 P) : (term291 A lt2 P) = False.
Proof. exact (prop_ext (fun h3 : term291 A lt2 P => @lem322328 A lt2 P h1 h2) (fun h3 : False => @lem320846 A lt2 P h2)). Qed.
Lemma lem322330 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) (h2 : term291 A lt2 P) : False.
Proof. exact (EQ_MP (@lem322329 A lt2 P h1 h2) (@lem320846 A lt2 P h2)). Qed.
Lemma lem322331 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term290 A lt2 P.
Proof. exact (fun h0 : term291 A lt2 P => @lem322330 A lt2 P h1 h0). Qed.
Lemma lem322332 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term289 A lt2 P.
Proof. exact (EQ_MP (@lem320845 A lt2 P) (@lem322331 A lt2 P h1)). Qed.
Lemma lem322333 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term288 A lt2 P.
Proof. exact (EQ_MP (@lem320841 A lt2 P) (@lem322332 A lt2 P h1)). Qed.
Lemma lem322334 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term9 A lt2 P) (h2 : term68 A P lt2) : term72 A P.
Proof. exact (@lem322333 A lt2 P h1 (@lem320663 A P lt2 h2)). Qed.
Lemma lem322335 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term86 A lt2 P.
Proof. exact (fun h0 : term68 A P lt2 => @lem322334 A P lt2 h1 h0). Qed.
Lemma lem322336 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term9 A lt2 P) (h2 : term45 A P lt2) : term74 A lt2 P.
Proof. exact (EQ_MP (@lem318999 A P lt2 h2) (@lem322335 A lt2 P h1)). Qed.
Lemma lem322337 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : (term45 A P lt2) = (term74 A lt2 P).
Proof. exact (prop_ext (fun h2 : term45 A P lt2 => @lem322336 A P lt2 h1 h2) (fun h2 : term74 A lt2 P => @lem320656 A P lt2)). Qed.
Lemma lem322338 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term74 A lt2 P.
Proof. exact (EQ_MP (@lem322337 A lt2 P h1) (@lem320656 A P lt2)). Qed.
Lemma lem322339 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term73 A lt2 P.
Proof. exact (EQ_MP (@lem318841 A lt2 P) (@lem322338 A lt2 P h1)). Qed.
Lemma lem322340 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term9 A lt2 P) (h2 : term8 A lt2) : term72 A P.
Proof. exact (@lem322339 A lt2 P h1 (@lem318514 A P lt2 h2)). Qed.
Lemma lem322341 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term8 A lt2) : term525 A lt2 P.
Proof. exact (fun h0 : term9 A lt2 P => @lem322340 A P lt2 h0 h1). Qed.
Lemma lem322346 {A : Type'} (lt2 : type1402 A) (h1 : term8 A lt2) : term4 A lt2.
Proof. exact (fun P : A -> Prop => @lem322341 A P lt2 h1). Qed.
Lemma lem322347 {A : Type'} (lt2 : type1402 A) : term7 A lt2.
Proof. exact (fun h0 : term8 A lt2 => @lem322346 A lt2 h0). Qed.
Lemma lem322348 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (EQ_MP (@lem318509 A lt2) (@lem322347 A lt2)). Qed.
