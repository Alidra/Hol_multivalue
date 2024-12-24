Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTER_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INTER_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Lemma lem3371486 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem3371487 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3371488 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3371487 A s) (@lem3371486 A s)). Qed.
Lemma lem3371489 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3371488 A s t). Qed.
Lemma lem3371490 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3371491 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3371490 A s t) (@lem3371489 A s t)). Qed.
Lemma lem3371492 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3371491 A s t x). Qed.
Lemma lem3371493 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s t x) = ((term5 A x s t) = (term6 A s x t)).
Proof. exact (eq_refl (term4 A s t x)). Qed.
Lemma lem3371495 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3371496 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem3371497 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem3371496 A B y) (@lem3371495 A B y)). Qed.
Lemma lem3371498 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem3371497 A B y s). Qed.
Lemma lem3371499 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem3371500 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem3371499 A B y s) (@lem3371498 A B y s)). Qed.
Lemma lem3371501 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem3371500 A B y s f). Qed.
Lemma lem3371502 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem3371504 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3371505 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3371506 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem3371505 A s) (@lem3371504 A s)). Qed.
Lemma lem3371507 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem3371506 A s t). Qed.
Lemma lem3371508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem3371547 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3371508 A s t) (@lem3371507 A s t)). Qed.
Lemma lem3371548 {_87658 : Type'} (s : _87658 -> Prop) (t : _87658 -> Prop) : (s = t) = (term17 _87658 s t).
Proof. exact (@lem3371547 _87658 s t). Qed.
Lemma lem3371549 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term18 _87647 _87658 f s t) = (term19 _87647 _87658 s f t)) = (term20 _87647 _87658 s f t).
Proof. exact (@lem3371548 _87658 (term18 _87647 _87658 f s t) (term19 _87647 _87658 s f t)). Qed.
Lemma lem3371559 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3371502 A B y f s) (@lem3371501 A B y s f)). Qed.
Lemma lem3371560 {_87647 _87658 : Type'} (y : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term12 _87647 _87658 y f s) = (term13 _87647 _87658 y f s).
Proof. exact (@lem3371559 _87647 _87658 y f s). Qed.
Lemma lem3371561 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term21 _87647 _87658 x f s t) = (term22 _87647 _87658 x f s t).
Proof. exact (@lem3371560 _87647 _87658 x f (@INTER _87647 s t)). Qed.
Lemma lem3371573 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3371493 A s x t) (@lem3371492 A s t x)). Qed.
Lemma lem3371574 {_87647 : Type'} (s : _87647 -> Prop) (x : _87647) (t : _87647 -> Prop) : (term5 _87647 x s t) = (term6 _87647 s x t).
Proof. exact (@lem3371573 _87647 s x t). Qed.
Lemma lem3371577 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) : (term23 _87647 _87658 x f x') = (term23 _87647 _87658 x f x').
Proof. exact (eq_refl (term23 _87647 _87658 x f x')). Qed.
Lemma lem3371578 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term24 _87647 _87658 x f x' s t) = (term25 _87647 _87658 x f s x' t).
Proof. exact (MK_COMB (@lem3371577 _87647 _87658 x f x') (@lem3371574 _87647 s x' t)). Qed.
Lemma lem3371581 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term26 _87647 _87658 x f s t) = (term27 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3371578 _87647 _87658 x f s x' t)). Qed.
Lemma lem3371582 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3371583 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term22 _87647 _87658 x f s t) = (term28 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3371582 _87647) (@lem3371581 _87647 _87658 x f s t)). Qed.
Lemma lem3371588 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term21 _87647 _87658 x f s t) = (term28 _87647 _87658 x f s t).
Proof. exact (TRANS (@lem3371561 _87647 _87658 x f s t) (@lem3371583 _87647 _87658 x f s t)). Qed.
Lemma lem3371589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3371590 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term29 _87647 _87658 x f s t) = (term30 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3371589) (@lem3371588 _87647 _87658 x f s t)). Qed.
Lemma lem3371592 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3371493 A s x t) (@lem3371492 A s t x)). Qed.
Lemma lem3371593 {_87658 : Type'} (s : _87658 -> Prop) (x : _87658) (t : _87658 -> Prop) : (term5 _87658 x s t) = (term6 _87658 s x t).
Proof. exact (@lem3371592 _87658 s x t). Qed.
Lemma lem3371594 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term31 _87647 _87658 x s f t) = (term32 _87647 _87658 s x f t).
Proof. exact (@lem3371593 _87658 (@IMAGE _87647 _87658 f s) x (@IMAGE _87647 _87658 f t)). Qed.
Lemma lem3371598 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3371502 A B y f s) (@lem3371501 A B y s f)). Qed.
Lemma lem3371599 {_87647 _87658 : Type'} (y : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term12 _87647 _87658 y f s) = (term13 _87647 _87658 y f s).
Proof. exact (@lem3371598 _87647 _87658 y f s). Qed.
Lemma lem3371600 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term12 _87647 _87658 x f s) = (term13 _87647 _87658 x f s).
Proof. exact (@lem3371599 _87647 _87658 x f s). Qed.
Lemma lem3371611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3371612 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term33 _87647 _87658 x f s) = (term34 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3371611) (@lem3371600 _87647 _87658 x f s)). Qed.
Lemma lem3371614 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3371502 A B y f s) (@lem3371501 A B y s f)). Qed.
Lemma lem3371615 {_87647 _87658 : Type'} (y : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term12 _87647 _87658 y f s) = (term13 _87647 _87658 y f s).
Proof. exact (@lem3371614 _87647 _87658 y f s). Qed.
Lemma lem3371616 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term12 _87647 _87658 x f t) = (term13 _87647 _87658 x f t).
Proof. exact (@lem3371615 _87647 _87658 x f t). Qed.
Lemma lem3371627 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term32 _87647 _87658 s x f t) = (term35 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3371612 _87647 _87658 x f s) (@lem3371616 _87647 _87658 x f t)). Qed.
Lemma lem3371630 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term31 _87647 _87658 x s f t) = (term35 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3371594 _87647 _87658 s x f t) (@lem3371627 _87647 _87658 s x f t)). Qed.
Lemma lem3371631 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term21 _87647 _87658 x f s t) = (term31 _87647 _87658 x s f t)) = ((term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t)).
Proof. exact (MK_COMB (@lem3371590 _87647 _87658 x f s t) (@lem3371630 _87647 _87658 s x f t)). Qed.
Lemma lem3371636 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term36 _87647 _87658 s f t) = (term37 _87647 _87658 s f t).
Proof. exact (fun_ext (fun x : _87658 => @lem3371631 _87647 _87658 s x f t)). Qed.
Lemma lem3371637 {_87658 : Type'} : (@all _87658) = (@all _87658).
Proof. exact (eq_refl (@all _87658)). Qed.
Lemma lem3371638 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term20 _87647 _87658 s f t) = (term38 _87647 _87658 s f t).
Proof. exact (MK_COMB (@lem3371637 _87658) (@lem3371636 _87647 _87658 s f t)). Qed.
Lemma lem3371643 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term18 _87647 _87658 f s t) = (term19 _87647 _87658 s f t)) = (term38 _87647 _87658 s f t).
Proof. exact (TRANS (@lem3371549 _87647 _87658 s f t) (@lem3371638 _87647 _87658 s f t)). Qed.
Lemma lem3371644 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term39 _87647 _87658 f) = (term39 _87647 _87658 f).
Proof. exact (eq_refl (term39 _87647 _87658 f)). Qed.
Lemma lem3371645 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term40 _87647 _87658 s f t) = (term41 _87647 _87658 s f t).
Proof. exact (MK_COMB (@lem3371644 _87647 _87658 f) (@lem3371643 _87647 _87658 s f t)). Qed.
Lemma lem3371648 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) : (term42 _87647 _87658 s f) = (term43 _87647 _87658 s f).
Proof. exact (fun_ext (fun t : _87647 -> Prop => @lem3371645 _87647 _87658 s f t)). Qed.
Lemma lem3371649 {_87647 : Type'} : (@all (_87647 -> Prop)) = (@all (_87647 -> Prop)).
Proof. exact (eq_refl (@all (_87647 -> Prop))). Qed.
Lemma lem3371650 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) : (term44 _87647 _87658 s f) = (term45 _87647 _87658 s f).
Proof. exact (MK_COMB (@lem3371649 _87647) (@lem3371648 _87647 _87658 s f)). Qed.
Lemma lem3371655 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term46 _87647 _87658 f) = (term47 _87647 _87658 f).
Proof. exact (fun_ext (fun s : _87647 -> Prop => @lem3371650 _87647 _87658 s f)). Qed.
Lemma lem3371656 {_87647 : Type'} : (@all (_87647 -> Prop)) = (@all (_87647 -> Prop)).
Proof. exact (eq_refl (@all (_87647 -> Prop))). Qed.
Lemma lem3371657 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term48 _87647 _87658 f) = (term49 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3371656 _87647) (@lem3371655 _87647 _87658 f)). Qed.
Lemma lem3371662 {_87647 _87658 : Type'} : (term50 _87647 _87658) = (term51 _87647 _87658).
Proof. exact (fun_ext (fun f : _87647 -> _87658 => @lem3371657 _87647 _87658 f)). Qed.
Lemma lem3371663 {_87647 _87658 : Type'} : (@all (_87647 -> _87658)) = (@all (_87647 -> _87658)).
Proof. exact (eq_refl (@all (_87647 -> _87658))). Qed.
Lemma lem3371664 {_87647 _87658 : Type'} : (term52 _87647 _87658) = (term53 _87647 _87658).
Proof. exact (MK_COMB (@lem3371663 _87647 _87658) (@lem3371662 _87647 _87658)). Qed.
Lemma lem3371669 {_87647 _87658 : Type'} : (term53 _87647 _87658) = (term52 _87647 _87658).
Proof. exact (SYM (@lem3371664 _87647 _87658)). Qed.
Lemma lem3371671 (p : Prop) : p = (term54 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3371672 {_87647 _87658 : Type'} : (term53 _87647 _87658) = (term55 _87647 _87658).
Proof. exact (@lem3371671 (term53 _87647 _87658)). Qed.
Lemma lem3371673 {_87647 _87658 : Type'} : (term55 _87647 _87658) = (term53 _87647 _87658).
Proof. exact (SYM (@lem3371672 _87647 _87658)). Qed.
Lemma lem3371674 {_87647 _87658 : Type'} (h1 : term56 _87647 _87658) : term56 _87647 _87658.
Proof. exact (h1). Qed.
Lemma lem3371677 {_87647 _87658 : Type'} (h1 : term55 _87647 _87658) : term55 _87647 _87658.
Proof. exact (h1). Qed.
Lemma lem3371678 {_87647 _87658 : Type'} : term57 _87647 _87658.
Proof. exact (fun h0 : term55 _87647 _87658 => @lem3371677 _87647 _87658 h0). Qed.
Lemma lem3371679 {_87647 _87658 : Type'} (h1 : term57 _87647 _87658) : term57 _87647 _87658.
Proof. exact (h1). Qed.
Lemma lem3371680 {_87647 _87658 : Type'} (h1 : term55 _87647 _87658) : term55 _87647 _87658.
Proof. exact (h1). Qed.
Lemma lem3371681 {_87647 _87658 : Type'} (h1 : term55 _87647 _87658) (h2 : term57 _87647 _87658) : term55 _87647 _87658.
Proof. exact (@lem3371679 _87647 _87658 h2 (@lem3371680 _87647 _87658 h1)). Qed.
Lemma lem3371682 {_87647 _87658 : Type'} (h1 : term55 _87647 _87658) : term58 _87647 _87658.
Proof. exact (fun h0 : term57 _87647 _87658 => @lem3371681 _87647 _87658 h1 h0). Qed.
Lemma lem3371683 {_87647 _87658 : Type'} (h1 : term57 _87647 _87658) : term57 _87647 _87658.
Proof. exact (h1). Qed.
Lemma lem3371684 {_87647 _87658 : Type'} (h1 : term55 _87647 _87658) (h2 : term57 _87647 _87658) : term55 _87647 _87658.
Proof. exact (@lem3371682 _87647 _87658 h1 (@lem3371683 _87647 _87658 h2)). Qed.
Lemma lem3371685 {_87647 _87658 : Type'} (h1 : term57 _87647 _87658) : term57 _87647 _87658.
Proof. exact (fun h0 : term55 _87647 _87658 => @lem3371684 _87647 _87658 h0 h1). Qed.
Lemma lem3371686 {_87647 _87658 : Type'} : term59 _87647 _87658.
Proof. exact (fun h0 : term57 _87647 _87658 => @lem3371685 _87647 _87658 h0). Qed.
Lemma lem3371689 {_87647 _87658 : Type'} : term57 _87647 _87658.
Proof. exact (@lem3371686 _87647 _87658 (@lem3371678 _87647 _87658)). Qed.
Lemma lem3371690 {_87647 _87658 : Type'} : term57 _87647 _87658.
Proof. exact (@lem3371689 _87647 _87658). Qed.
Lemma lem3371692 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3371693 {_87647 _87658 : Type'} : (term55 _87647 _87658) = (term60 _87647 _87658).
Proof. exact (@lem3371692 (term56 _87647 _87658)). Qed.
Lemma lem3371695 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3371696 {_87647 _87658 : Type'} : (term60 _87647 _87658) = (term53 _87647 _87658).
Proof. exact (@lem3371695 (term53 _87647 _87658)). Qed.
Lemma lem3371883 {_87647 _87658 : Type'} : (term55 _87647 _87658) = (term53 _87647 _87658).
Proof. exact (TRANS (@lem3371693 _87647 _87658) (@lem3371696 _87647 _87658)). Qed.
Lemma lem3371888 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term62 _87647 _87658 x f x' t) = (term62 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term62 _87647 _87658 x f x' t)). Qed.
Lemma lem3371889 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term63 _87647 _87658 x f t) = (term63 _87647 _87658 x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3371888 _87647 _87658 x f x' t)). Qed.
Lemma lem3371890 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3371891 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term13 _87647 _87658 x f t) = (term13 _87647 _87658 x f t).
Proof. exact (MK_COMB (@lem3371890 _87647) (@lem3371889 _87647 _87658 x f t)). Qed.
Lemma lem3371896 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term62 _87647 _87658 x f x' s) = (term62 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term62 _87647 _87658 x f x' s)). Qed.
Lemma lem3371897 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term63 _87647 _87658 x f s) = (term63 _87647 _87658 x f s).
Proof. exact (fun_ext (fun x' : _87647 => @lem3371896 _87647 _87658 x f x' s)). Qed.
Lemma lem3371898 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3371899 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term13 _87647 _87658 x f s) = (term13 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3371898 _87647) (@lem3371897 _87647 _87658 x f s)). Qed.
Lemma lem3371900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3371901 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term34 _87647 _87658 x f s) = (term34 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3371900) (@lem3371899 _87647 _87658 x f s)). Qed.
Lemma lem3371902 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term35 _87647 _87658 s x f t) = (term35 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3371901 _87647 _87658 x f s) (@lem3371891 _87647 _87658 x f t)). Qed.
Lemma lem3371911 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term25 _87647 _87658 x f s x' t) = (term25 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term25 _87647 _87658 x f s x' t)). Qed.
Lemma lem3371912 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term27 _87647 _87658 x f s t) = (term27 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3371911 _87647 _87658 x f s x' t)). Qed.
Lemma lem3371913 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3371914 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term28 _87647 _87658 x f s t) = (term28 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3371913 _87647) (@lem3371912 _87647 _87658 x f s t)). Qed.
Lemma lem3371915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3371916 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term30 _87647 _87658 x f s t) = (term30 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3371915) (@lem3371914 _87647 _87658 x f s t)). Qed.
Lemma lem3371917 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t)) = ((term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t)).
Proof. exact (MK_COMB (@lem3371916 _87647 _87658 x f s t) (@lem3371902 _87647 _87658 s x f t)). Qed.
Lemma lem3371918 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term37 _87647 _87658 s f t) = (term37 _87647 _87658 s f t).
Proof. exact (fun_ext (fun x : _87658 => @lem3371917 _87647 _87658 s x f t)). Qed.
Lemma lem3371919 {_87658 : Type'} : (@all _87658) = (@all _87658).
Proof. exact (eq_refl (@all _87658)). Qed.
Lemma lem3371920 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term38 _87647 _87658 s f t) = (term38 _87647 _87658 s f t).
Proof. exact (MK_COMB (@lem3371919 _87658) (@lem3371918 _87647 _87658 s f t)). Qed.
Lemma lem3371925 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) (y : _87647) : (term64 _87647 _87658 f x y) = (term64 _87647 _87658 f x y).
Proof. exact (eq_refl (term64 _87647 _87658 f x y)). Qed.
Lemma lem3371926 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term65 _87647 _87658 f x) = (term65 _87647 _87658 f x).
Proof. exact (fun_ext (fun y : _87647 => @lem3371925 _87647 _87658 f x y)). Qed.
Lemma lem3371927 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3371928 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term66 _87647 _87658 f x) = (term66 _87647 _87658 f x).
Proof. exact (MK_COMB (@lem3371927 _87647) (@lem3371926 _87647 _87658 f x)). Qed.
Lemma lem3371929 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term67 _87647 _87658 f) = (term67 _87647 _87658 f).
Proof. exact (fun_ext (fun x : _87647 => @lem3371928 _87647 _87658 f x)). Qed.
Lemma lem3371930 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3371931 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term68 _87647 _87658 f) = (term68 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3371930 _87647) (@lem3371929 _87647 _87658 f)). Qed.
Lemma lem3371932 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3371933 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term39 _87647 _87658 f) = (term39 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3371932) (@lem3371931 _87647 _87658 f)). Qed.
Lemma lem3371934 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term41 _87647 _87658 s f t) = (term41 _87647 _87658 s f t).
Proof. exact (MK_COMB (@lem3371933 _87647 _87658 f) (@lem3371920 _87647 _87658 s f t)). Qed.
Lemma lem3371935 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) : (term43 _87647 _87658 s f) = (term43 _87647 _87658 s f).
Proof. exact (fun_ext (fun t : _87647 -> Prop => @lem3371934 _87647 _87658 s f t)). Qed.
Lemma lem3371936 {_87647 : Type'} : (@all (_87647 -> Prop)) = (@all (_87647 -> Prop)).
Proof. exact (eq_refl (@all (_87647 -> Prop))). Qed.
Lemma lem3371937 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) : (term45 _87647 _87658 s f) = (term45 _87647 _87658 s f).
Proof. exact (MK_COMB (@lem3371936 _87647) (@lem3371935 _87647 _87658 s f)). Qed.
Lemma lem3371938 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term47 _87647 _87658 f) = (term47 _87647 _87658 f).
Proof. exact (fun_ext (fun s : _87647 -> Prop => @lem3371937 _87647 _87658 s f)). Qed.
Lemma lem3371939 {_87647 : Type'} : (@all (_87647 -> Prop)) = (@all (_87647 -> Prop)).
Proof. exact (eq_refl (@all (_87647 -> Prop))). Qed.
Lemma lem3371940 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term49 _87647 _87658 f) = (term49 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3371939 _87647) (@lem3371938 _87647 _87658 f)). Qed.
Lemma lem3371941 {_87647 _87658 : Type'} : (term51 _87647 _87658) = (term51 _87647 _87658).
Proof. exact (fun_ext (fun f : _87647 -> _87658 => @lem3371940 _87647 _87658 f)). Qed.
Lemma lem3371942 {_87647 _87658 : Type'} : (@all (_87647 -> _87658)) = (@all (_87647 -> _87658)).
Proof. exact (eq_refl (@all (_87647 -> _87658))). Qed.
Lemma lem3371943 {_87647 _87658 : Type'} : (term53 _87647 _87658) = (term53 _87647 _87658).
Proof. exact (MK_COMB (@lem3371942 _87647 _87658) (@lem3371941 _87647 _87658)). Qed.
Lemma lem3372014 {_87647 _87658 : Type'} : (term55 _87647 _87658) = (term53 _87647 _87658).
Proof. exact (TRANS (@lem3371883 _87647 _87658) (@lem3371943 _87647 _87658)). Qed.
Lemma lem3372015 {_87647 _87658 : Type'} : (term53 _87647 _87658) = (term55 _87647 _87658).
Proof. exact (SYM (@lem3372014 _87647 _87658)). Qed.
Lemma lem3372016 {_87647 _87658 : Type'} (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term68 _87647 _87658 f.
Proof. exact (h1). Qed.
Lemma lem3372018 (p : Prop) : p = (term54 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3372019 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t)) = (term69 _87647 _87658 s x f t).
Proof. exact (@lem3372018 ((term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t))). Qed.
Lemma lem3372020 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term69 _87647 _87658 s x f t) = ((term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t)).
Proof. exact (SYM (@lem3372019 _87647 _87658 s x f t)). Qed.
Lemma lem3372021 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term70 _87647 _87658 s x f t) : term70 _87647 _87658 s x f t.
Proof. exact (h1). Qed.
Lemma lem3372028 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) (y : _87647) : (term64 _87647 _87658 f x y) = (term71 _87647 _87658 f x y).
Proof. exact (@lem17265 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3372029 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term65 _87647 _87658 f x) = (term72 _87647 _87658 f x).
Proof. exact (fun_ext (fun y : _87647 => @lem3372028 _87647 _87658 f x y)). Qed.
Lemma lem3372030 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372031 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term66 _87647 _87658 f x) = (term73 _87647 _87658 f x).
Proof. exact (MK_COMB (@lem3372030 _87647) (@lem3372029 _87647 _87658 f x)). Qed.
Lemma lem3372032 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term67 _87647 _87658 f) = (term74 _87647 _87658 f).
Proof. exact (fun_ext (fun x : _87647 => @lem3372031 _87647 _87658 f x)). Qed.
Lemma lem3372033 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372090 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term68 _87647 _87658 f) = (term75 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3372033 _87647) (@lem3372032 _87647 _87658 f)). Qed.
Lemma lem3372091 {_87647 _87658 : Type'} (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term75 _87647 _87658 f.
Proof. exact (EQ_MP (@lem3372090 _87647 _87658 f) (@lem3372016 _87647 _87658 f h1)). Qed.
Lemma lem3372102 {_87647 : Type'} (s : _87647 -> Prop) (x : _87647) (t : _87647 -> Prop) : (term76 _87647 s x t) = (term77 _87647 s x t).
Proof. exact (@lem17045 (@IN _87647 x s) (@IN _87647 x t)). Qed.
Lemma lem3372107 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) : (term78 _87647 _87658 x f x') = (term78 _87647 _87658 x f x').
Proof. exact (eq_refl (term78 _87647 _87658 x f x')). Qed.
Lemma lem3372108 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term79 _87647 _87658 x f s x' t) = (term80 _87647 _87658 x f s x' t).
Proof. exact (MK_COMB (@lem3372107 _87647 _87658 x f x') (@lem3372102 _87647 s x' t)). Qed.
Lemma lem3372109 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term81 _87647 _87658 x f s x' t) = (term79 _87647 _87658 x f s x' t).
Proof. exact (@lem17045 (x = (f x')) (term6 _87647 s x' t)). Qed.
Lemma lem3372110 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term81 _87647 _87658 x f s x' t) = (term80 _87647 _87658 x f s x' t).
Proof. exact (TRANS (@lem3372109 _87647 _87658 x f s x' t) (@lem3372108 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372113 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term25 _87647 _87658 x f s x' t) = (term25 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term25 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372114 {_87647 : Type'} (P : _87647 -> Prop) : (term82 _87647 P) = (term83 _87647 P).
Proof. exact (@lem18394 _87647 P). Qed.
Lemma lem3372115 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term84 _87647 _87658 x f s t) = (term85 _87647 _87658 x f s t).
Proof. exact (@lem3372114 _87647 (term27 _87647 _87658 x f s t)). Qed.
Lemma lem3372116 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term86 _87647 _87658 x f s t x') = (term25 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term86 _87647 _87658 x f s t x')). Qed.
Lemma lem3372117 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3372118 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term87 _87647 _87658 x f s t x') = (term81 _87647 _87658 x f s x' t).
Proof. exact (MK_COMB (@lem3372117) (@lem3372116 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372119 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term87 _87647 _87658 x f s t x') = (term80 _87647 _87658 x f s x' t).
Proof. exact (TRANS (@lem3372118 _87647 _87658 x f s x' t) (@lem3372110 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372120 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term88 _87647 _87658 x f s t) = (term89 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372119 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372121 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372122 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term85 _87647 _87658 x f s t) = (term90 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372121 _87647) (@lem3372120 _87647 _87658 x f s t)). Qed.
Lemma lem3372123 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term84 _87647 _87658 x f s t) = (term90 _87647 _87658 x f s t).
Proof. exact (TRANS (@lem3372115 _87647 _87658 x f s t) (@lem3372122 _87647 _87658 x f s t)). Qed.
Lemma lem3372124 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term27 _87647 _87658 x f s t) = (term27 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372113 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372125 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372126 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term28 _87647 _87658 x f s t) = (term28 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372125 _87647) (@lem3372124 _87647 _87658 x f s t)). Qed.
Lemma lem3372135 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term91 _87647 _87658 x f x' s) = (term92 _87647 _87658 x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN _87647 x' s)). Qed.
Lemma lem3372138 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term62 _87647 _87658 x f x' s) = (term62 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term62 _87647 _87658 x f x' s)). Qed.
Lemma lem3372139 {_87647 : Type'} (P : _87647 -> Prop) : (term82 _87647 P) = (term83 _87647 P).
Proof. exact (@lem18394 _87647 P). Qed.
Lemma lem3372140 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term93 _87647 _87658 x f s) = (term94 _87647 _87658 x f s).
Proof. exact (@lem3372139 _87647 (term63 _87647 _87658 x f s)). Qed.
Lemma lem3372141 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term95 _87647 _87658 x f s x') = (term62 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term95 _87647 _87658 x f s x')). Qed.
Lemma lem3372142 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3372143 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term96 _87647 _87658 x f s x') = (term91 _87647 _87658 x f x' s).
Proof. exact (MK_COMB (@lem3372142) (@lem3372141 _87647 _87658 x f x' s)). Qed.
Lemma lem3372144 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term96 _87647 _87658 x f s x') = (term92 _87647 _87658 x f x' s).
Proof. exact (TRANS (@lem3372143 _87647 _87658 x f x' s) (@lem3372135 _87647 _87658 x f x' s)). Qed.
Lemma lem3372145 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term97 _87647 _87658 x f s) = (term98 _87647 _87658 x f s).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372144 _87647 _87658 x f x' s)). Qed.
Lemma lem3372146 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372147 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term94 _87647 _87658 x f s) = (term99 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372146 _87647) (@lem3372145 _87647 _87658 x f s)). Qed.
Lemma lem3372148 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term93 _87647 _87658 x f s) = (term99 _87647 _87658 x f s).
Proof. exact (TRANS (@lem3372140 _87647 _87658 x f s) (@lem3372147 _87647 _87658 x f s)). Qed.
Lemma lem3372149 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term63 _87647 _87658 x f s) = (term63 _87647 _87658 x f s).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372138 _87647 _87658 x f x' s)). Qed.
Lemma lem3372150 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372151 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term13 _87647 _87658 x f s) = (term13 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372150 _87647) (@lem3372149 _87647 _87658 x f s)). Qed.
Lemma lem3372160 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term91 _87647 _87658 x f x' t) = (term92 _87647 _87658 x f x' t).
Proof. exact (@lem17045 (x = (f x')) (@IN _87647 x' t)). Qed.
Lemma lem3372163 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term62 _87647 _87658 x f x' t) = (term62 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term62 _87647 _87658 x f x' t)). Qed.
Lemma lem3372164 {_87647 : Type'} (P : _87647 -> Prop) : (term82 _87647 P) = (term83 _87647 P).
Proof. exact (@lem18394 _87647 P). Qed.
Lemma lem3372165 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term93 _87647 _87658 x f t) = (term94 _87647 _87658 x f t).
Proof. exact (@lem3372164 _87647 (term63 _87647 _87658 x f t)). Qed.
Lemma lem3372166 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term95 _87647 _87658 x f t x') = (term62 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term95 _87647 _87658 x f t x')). Qed.
Lemma lem3372167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3372168 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term96 _87647 _87658 x f t x') = (term91 _87647 _87658 x f x' t).
Proof. exact (MK_COMB (@lem3372167) (@lem3372166 _87647 _87658 x f x' t)). Qed.
Lemma lem3372169 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term96 _87647 _87658 x f t x') = (term92 _87647 _87658 x f x' t).
Proof. exact (TRANS (@lem3372168 _87647 _87658 x f x' t) (@lem3372160 _87647 _87658 x f x' t)). Qed.
Lemma lem3372170 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term97 _87647 _87658 x f t) = (term98 _87647 _87658 x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372169 _87647 _87658 x f x' t)). Qed.
Lemma lem3372171 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372172 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term94 _87647 _87658 x f t) = (term99 _87647 _87658 x f t).
Proof. exact (MK_COMB (@lem3372171 _87647) (@lem3372170 _87647 _87658 x f t)). Qed.
Lemma lem3372173 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term93 _87647 _87658 x f t) = (term99 _87647 _87658 x f t).
Proof. exact (TRANS (@lem3372165 _87647 _87658 x f t) (@lem3372172 _87647 _87658 x f t)). Qed.
Lemma lem3372174 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term63 _87647 _87658 x f t) = (term63 _87647 _87658 x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372163 _87647 _87658 x f x' t)). Qed.
Lemma lem3372175 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372176 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term13 _87647 _87658 x f t) = (term13 _87647 _87658 x f t).
Proof. exact (MK_COMB (@lem3372175 _87647) (@lem3372174 _87647 _87658 x f t)). Qed.
Lemma lem3372177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372178 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term100 _87647 _87658 x f s) = (term101 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372177) (@lem3372148 _87647 _87658 x f s)). Qed.
Lemma lem3372179 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term102 _87647 _87658 s x f t) = (term103 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372178 _87647 _87658 x f s) (@lem3372173 _87647 _87658 x f t)). Qed.
Lemma lem3372180 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term104 _87647 _87658 s x f t) = (term102 _87647 _87658 s x f t).
Proof. exact (@lem17045 (term13 _87647 _87658 x f s) (term13 _87647 _87658 x f t)). Qed.
Lemma lem3372181 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term104 _87647 _87658 s x f t) = (term103 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372180 _87647 _87658 s x f t) (@lem3372179 _87647 _87658 s x f t)). Qed.
Lemma lem3372182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372183 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term34 _87647 _87658 x f s) = (term34 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372182) (@lem3372151 _87647 _87658 x f s)). Qed.
Lemma lem3372184 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term35 _87647 _87658 s x f t) = (term35 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372183 _87647 _87658 x f s) (@lem3372176 _87647 _87658 x f t)). Qed.
Lemma lem3372185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372186 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term105 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372185) (@lem3372123 _87647 _87658 x f s t)). Qed.
Lemma lem3372187 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term107 _87647 _87658 s x f t) = (term108 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372186 _87647 _87658 x f s t) (@lem3372184 _87647 _87658 s x f t)). Qed.
Lemma lem3372188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372189 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term109 _87647 _87658 x f s t) = (term109 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372188) (@lem3372126 _87647 _87658 x f s t)). Qed.
Lemma lem3372190 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term110 _87647 _87658 s x f t) = (term111 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372189 _87647 _87658 x f s t) (@lem3372181 _87647 _87658 s x f t)). Qed.
Lemma lem3372191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372192 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term112 _87647 _87658 s x f t) = (term113 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372191) (@lem3372190 _87647 _87658 s x f t)). Qed.
Lemma lem3372193 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term114 _87647 _87658 s x f t) = (term115 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372192 _87647 _87658 s x f t) (@lem3372187 _87647 _87658 s x f t)). Qed.
Lemma lem3372194 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term70 _87647 _87658 s x f t) = (term114 _87647 _87658 s x f t).
Proof. exact (@lem17646 (term28 _87647 _87658 x f s t) (term35 _87647 _87658 s x f t)). Qed.
Lemma lem3372195 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term70 _87647 _87658 s x f t) = (term115 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372194 _87647 _87658 s x f t) (@lem3372193 _87647 _87658 s x f t)). Qed.
Lemma lem3372486 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3372487 {_87647 : Type'} (P : _87647 -> Prop) (Q : Prop) : (term116 _87647 P Q) = (term117 _87647 P Q).
Proof. exact (@lem3372486 _87647 P Q). Qed.
Lemma lem3372488 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term118 _87647 _87658 s x f t) = (term119 _87647 _87658 s x f t).
Proof. exact (@lem3372487 _87647 (term27 _87647 _87658 x f s t) (term103 _87647 _87658 s x f t)). Qed.
Lemma lem3372489 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term86 _87647 _87658 x f s t x') = (term25 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term86 _87647 _87658 x f s t x')). Qed.
Lemma lem3372490 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term120 _87647 _87658 x f s t) = (term27 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372489 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372491 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372492 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term121 _87647 _87658 x f s t) = (term28 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372491 _87647) (@lem3372490 _87647 _87658 x f s t)). Qed.
Lemma lem3372493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372494 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term122 _87647 _87658 x f s t) = (term109 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372493) (@lem3372492 _87647 _87658 x f s t)). Qed.
Lemma lem3372495 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term103 _87647 _87658 s x f t) = (term103 _87647 _87658 s x f t).
Proof. exact (eq_refl (term103 _87647 _87658 s x f t)). Qed.
Lemma lem3372496 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term118 _87647 _87658 s x f t) = (term111 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372494 _87647 _87658 x f s t) (@lem3372495 _87647 _87658 s x f t)). Qed.
Lemma lem3372497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372498 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term123 _87647 _87658 s x f t) = (term124 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372497) (@lem3372496 _87647 _87658 s x f t)). Qed.
Lemma lem3372499 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term86 _87647 _87658 x f s t x') = (term25 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term86 _87647 _87658 x f s t x')). Qed.
Lemma lem3372500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372501 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term125 _87647 _87658 x f s t x') = (term126 _87647 _87658 x f s x' t).
Proof. exact (MK_COMB (@lem3372500) (@lem3372499 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372502 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term103 _87647 _87658 s x f t) = (term103 _87647 _87658 s x f t).
Proof. exact (eq_refl (term103 _87647 _87658 s x f t)). Qed.
Lemma lem3372503 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term127 _87647 _87658 x s x' f t) = (term128 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372501 _87647 _87658 x' f s x t) (@lem3372502 _87647 _87658 s x' f t)). Qed.
Lemma lem3372504 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term129 _87647 _87658 s x f t) = (term130 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372503 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372505 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372506 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term119 _87647 _87658 s x f t) = (term131 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372505 _87647) (@lem3372504 _87647 _87658 s x f t)). Qed.
Lemma lem3372507 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term118 _87647 _87658 s x f t) = (term119 _87647 _87658 s x f t)) = ((term111 _87647 _87658 s x f t) = (term131 _87647 _87658 s x f t)).
Proof. exact (MK_COMB (@lem3372498 _87647 _87658 s x f t) (@lem3372506 _87647 _87658 s x f t)). Qed.
Lemma lem3372508 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term111 _87647 _87658 s x f t) = (term131 _87647 _87658 s x f t).
Proof. exact (EQ_MP (@lem3372507 _87647 _87658 s x f t) (@lem3372488 _87647 _87658 s x f t)). Qed.
Lemma lem3372509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372510 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term113 _87647 _87658 s x f t) = (term132 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372509) (@lem3372508 _87647 _87658 s x f t)). Qed.
Lemma lem3372512 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3372513 {_87647 : Type'} (P : _87647 -> Prop) (Q : Prop) : (term116 _87647 P Q) = (term117 _87647 P Q).
Proof. exact (@lem3372512 _87647 P Q). Qed.
Lemma lem3372514 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term133 _87647 _87658 s x f t) = (term134 _87647 _87658 s x f t).
Proof. exact (@lem3372513 _87647 (term63 _87647 _87658 x f s) (term13 _87647 _87658 x f t)). Qed.
Lemma lem3372515 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term95 _87647 _87658 x f s x') = (term62 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term95 _87647 _87658 x f s x')). Qed.
Lemma lem3372516 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term135 _87647 _87658 x f s) = (term63 _87647 _87658 x f s).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372515 _87647 _87658 x f x' s)). Qed.
Lemma lem3372517 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372518 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term136 _87647 _87658 x f s) = (term13 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372517 _87647) (@lem3372516 _87647 _87658 x f s)). Qed.
Lemma lem3372519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372520 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term137 _87647 _87658 x f s) = (term34 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372519) (@lem3372518 _87647 _87658 x f s)). Qed.
Lemma lem3372521 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term13 _87647 _87658 x f t) = (term13 _87647 _87658 x f t).
Proof. exact (eq_refl (term13 _87647 _87658 x f t)). Qed.
Lemma lem3372522 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term133 _87647 _87658 s x f t) = (term35 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372520 _87647 _87658 x f s) (@lem3372521 _87647 _87658 x f t)). Qed.
Lemma lem3372523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372524 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term138 _87647 _87658 s x f t) = (term139 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372523) (@lem3372522 _87647 _87658 s x f t)). Qed.
Lemma lem3372525 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term95 _87647 _87658 x f s x') = (term62 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term95 _87647 _87658 x f s x')). Qed.
Lemma lem3372526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372527 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term140 _87647 _87658 x f s x') = (term141 _87647 _87658 x f x' s).
Proof. exact (MK_COMB (@lem3372526) (@lem3372525 _87647 _87658 x f x' s)). Qed.
Lemma lem3372528 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term13 _87647 _87658 x f t) = (term13 _87647 _87658 x f t).
Proof. exact (eq_refl (term13 _87647 _87658 x f t)). Qed.
Lemma lem3372529 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term142 _87647 _87658 s x x' f t) = (term143 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372527 _87647 _87658 x' f x s) (@lem3372528 _87647 _87658 x' f t)). Qed.
Lemma lem3372530 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term144 _87647 _87658 s x f t) = (term145 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372529 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372531 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372532 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term134 _87647 _87658 s x f t) = (term146 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372531 _87647) (@lem3372530 _87647 _87658 s x f t)). Qed.
Lemma lem3372533 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term133 _87647 _87658 s x f t) = (term134 _87647 _87658 s x f t)) = ((term35 _87647 _87658 s x f t) = (term146 _87647 _87658 s x f t)).
Proof. exact (MK_COMB (@lem3372524 _87647 _87658 s x f t) (@lem3372532 _87647 _87658 s x f t)). Qed.
Lemma lem3372534 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term35 _87647 _87658 s x f t) = (term146 _87647 _87658 s x f t).
Proof. exact (EQ_MP (@lem3372533 _87647 _87658 s x f t) (@lem3372514 _87647 _87658 s x f t)). Qed.
Lemma lem3372536 {A : Type'} (P : Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3372537 {_87647 : Type'} (P : Prop) (Q : _87647 -> Prop) : (term147 _87647 P Q) = (term148 _87647 P Q).
Proof. exact (@lem3372536 _87647 P Q). Qed.
Lemma lem3372538 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term149 _87647 _87658 x s x' f t) = (term150 _87647 _87658 x s x' f t).
Proof. exact (@lem3372537 _87647 (term62 _87647 _87658 x' f x s) (term63 _87647 _87658 x' f t)). Qed.
Lemma lem3372539 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term95 _87647 _87658 x f t x') = (term62 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term95 _87647 _87658 x f t x')). Qed.
Lemma lem3372540 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term135 _87647 _87658 x f t) = (term63 _87647 _87658 x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372539 _87647 _87658 x f x' t)). Qed.
Lemma lem3372541 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372542 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term136 _87647 _87658 x f t) = (term13 _87647 _87658 x f t).
Proof. exact (MK_COMB (@lem3372541 _87647) (@lem3372540 _87647 _87658 x f t)). Qed.
Lemma lem3372543 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term141 _87647 _87658 x f x' s) = (term141 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term141 _87647 _87658 x f x' s)). Qed.
Lemma lem3372544 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term149 _87647 _87658 x s x' f t) = (term143 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372543 _87647 _87658 x' f x s) (@lem3372542 _87647 _87658 x' f t)). Qed.
Lemma lem3372545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372546 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term151 _87647 _87658 x s x' f t) = (term152 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372545) (@lem3372544 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372547 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term95 _87647 _87658 x f t x') = (term62 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term95 _87647 _87658 x f t x')). Qed.
Lemma lem3372548 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term141 _87647 _87658 x f x' s) = (term141 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term141 _87647 _87658 x f x' s)). Qed.
Lemma lem3372549 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term153 _87647 _87658 x s x' f t x'') = (term154 _87647 _87658 x s x' f x'' t).
Proof. exact (MK_COMB (@lem3372548 _87647 _87658 x' f x s) (@lem3372547 _87647 _87658 x' f x'' t)). Qed.
Lemma lem3372550 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term155 _87647 _87658 x s x' f t) = (term156 _87647 _87658 x s x' f t).
Proof. exact (fun_ext (fun x'' : _87647 => @lem3372549 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372551 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372552 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term150 _87647 _87658 x s x' f t) = (term157 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372551 _87647) (@lem3372550 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372553 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term149 _87647 _87658 x s x' f t) = (term150 _87647 _87658 x s x' f t)) = ((term143 _87647 _87658 x s x' f t) = (term157 _87647 _87658 x s x' f t)).
Proof. exact (MK_COMB (@lem3372546 _87647 _87658 x s x' f t) (@lem3372552 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372554 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term143 _87647 _87658 x s x' f t) = (term157 _87647 _87658 x s x' f t).
Proof. exact (EQ_MP (@lem3372553 _87647 _87658 x s x' f t) (@lem3372538 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372555 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term145 _87647 _87658 s x f t) = (term158 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372554 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372556 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372557 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term146 _87647 _87658 s x f t) = (term159 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372556 _87647) (@lem3372555 _87647 _87658 s x f t)). Qed.
Lemma lem3372558 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term35 _87647 _87658 s x f t) = (term159 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372534 _87647 _87658 s x f t) (@lem3372557 _87647 _87658 s x f t)). Qed.
Lemma lem3372559 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term106 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (eq_refl (term106 _87647 _87658 x f s t)). Qed.
Lemma lem3372560 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term108 _87647 _87658 s x f t) = (term160 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372559 _87647 _87658 x f s t) (@lem3372558 _87647 _87658 s x f t)). Qed.
Lemma lem3372562 {A : Type'} (P : Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3372563 {_87647 : Type'} (P : Prop) (Q : _87647 -> Prop) : (term147 _87647 P Q) = (term148 _87647 P Q).
Proof. exact (@lem3372562 _87647 P Q). Qed.
Lemma lem3372564 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term161 _87647 _87658 s x f t) = (term162 _87647 _87658 s x f t).
Proof. exact (@lem3372563 _87647 (term90 _87647 _87658 x f s t) (term158 _87647 _87658 s x f t)). Qed.
Lemma lem3372565 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term163 _87647 _87658 s x' f t x) = (term157 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term163 _87647 _87658 s x' f t x)). Qed.
Lemma lem3372566 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term164 _87647 _87658 s x f t) = (term158 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372565 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372567 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372568 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term165 _87647 _87658 s x f t) = (term159 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372567 _87647) (@lem3372566 _87647 _87658 s x f t)). Qed.
Lemma lem3372569 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term106 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (eq_refl (term106 _87647 _87658 x f s t)). Qed.
Lemma lem3372570 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term161 _87647 _87658 s x f t) = (term160 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372569 _87647 _87658 x f s t) (@lem3372568 _87647 _87658 s x f t)). Qed.
Lemma lem3372571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372572 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term166 _87647 _87658 s x f t) = (term167 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372571) (@lem3372570 _87647 _87658 s x f t)). Qed.
Lemma lem3372573 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term163 _87647 _87658 s x' f t x) = (term157 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term163 _87647 _87658 s x' f t x)). Qed.
Lemma lem3372574 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term106 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (eq_refl (term106 _87647 _87658 x f s t)). Qed.
Lemma lem3372575 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term168 _87647 _87658 s x' f t x) = (term169 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372574 _87647 _87658 x' f s t) (@lem3372573 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372576 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term170 _87647 _87658 s x f t) = (term171 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372575 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372577 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372578 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term162 _87647 _87658 s x f t) = (term172 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372577 _87647) (@lem3372576 _87647 _87658 s x f t)). Qed.
Lemma lem3372579 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term161 _87647 _87658 s x f t) = (term162 _87647 _87658 s x f t)) = ((term160 _87647 _87658 s x f t) = (term172 _87647 _87658 s x f t)).
Proof. exact (MK_COMB (@lem3372572 _87647 _87658 s x f t) (@lem3372578 _87647 _87658 s x f t)). Qed.
Lemma lem3372580 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term160 _87647 _87658 s x f t) = (term172 _87647 _87658 s x f t).
Proof. exact (EQ_MP (@lem3372579 _87647 _87658 s x f t) (@lem3372564 _87647 _87658 s x f t)). Qed.
Lemma lem3372582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3372583 {_87647 : Type'} (P : Prop) (Q : _87647 -> Prop) : (term147 _87647 P Q) = (term148 _87647 P Q).
Proof. exact (@lem3372582 _87647 P Q). Qed.
Lemma lem3372584 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term173 _87647 _87658 x s x' f t) = (term174 _87647 _87658 x s x' f t).
Proof. exact (@lem3372583 _87647 (term90 _87647 _87658 x' f s t) (term156 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372585 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term175 _87647 _87658 x s x' f t x'') = (term154 _87647 _87658 x s x' f x'' t).
Proof. exact (eq_refl (term175 _87647 _87658 x s x' f t x'')). Qed.
Lemma lem3372586 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term176 _87647 _87658 x s x' f t) = (term156 _87647 _87658 x s x' f t).
Proof. exact (fun_ext (fun x'' : _87647 => @lem3372585 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372587 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372588 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term177 _87647 _87658 x s x' f t) = (term157 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372587 _87647) (@lem3372586 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372589 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term106 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (eq_refl (term106 _87647 _87658 x f s t)). Qed.
Lemma lem3372590 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term173 _87647 _87658 x s x' f t) = (term169 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372589 _87647 _87658 x' f s t) (@lem3372588 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372592 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term178 _87647 _87658 x s x' f t) = (term179 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372591) (@lem3372590 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372593 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term175 _87647 _87658 x s x' f t x'') = (term154 _87647 _87658 x s x' f x'' t).
Proof. exact (eq_refl (term175 _87647 _87658 x s x' f t x'')). Qed.
Lemma lem3372594 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term106 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (eq_refl (term106 _87647 _87658 x f s t)). Qed.
Lemma lem3372595 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term180 _87647 _87658 x s x' f t x'') = (term181 _87647 _87658 x s x' f x'' t).
Proof. exact (MK_COMB (@lem3372594 _87647 _87658 x' f s t) (@lem3372593 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372596 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term182 _87647 _87658 x s x' f t) = (term183 _87647 _87658 x s x' f t).
Proof. exact (fun_ext (fun x'' : _87647 => @lem3372595 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372597 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372598 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term174 _87647 _87658 x s x' f t) = (term184 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372597 _87647) (@lem3372596 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372599 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term173 _87647 _87658 x s x' f t) = (term174 _87647 _87658 x s x' f t)) = ((term169 _87647 _87658 x s x' f t) = (term184 _87647 _87658 x s x' f t)).
Proof. exact (MK_COMB (@lem3372592 _87647 _87658 x s x' f t) (@lem3372598 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372600 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term169 _87647 _87658 x s x' f t) = (term184 _87647 _87658 x s x' f t).
Proof. exact (EQ_MP (@lem3372599 _87647 _87658 x s x' f t) (@lem3372584 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372601 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term171 _87647 _87658 s x f t) = (term185 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372600 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372602 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372603 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term172 _87647 _87658 s x f t) = (term186 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372602 _87647) (@lem3372601 _87647 _87658 s x f t)). Qed.
Lemma lem3372604 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term160 _87647 _87658 s x f t) = (term186 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372580 _87647 _87658 s x f t) (@lem3372603 _87647 _87658 s x f t)). Qed.
Lemma lem3372605 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term108 _87647 _87658 s x f t) = (term186 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372560 _87647 _87658 s x f t) (@lem3372604 _87647 _87658 s x f t)). Qed.
Lemma lem3372606 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term115 _87647 _87658 s x f t) = (term187 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372510 _87647 _87658 s x f t) (@lem3372605 _87647 _87658 s x f t)). Qed.
Lemma lem3372608 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3372609 {_87647 : Type'} (P : _87647 -> Prop) (Q : _87647 -> Prop) : (term188 _87647 P Q) = (term189 _87647 P Q).
Proof. exact (@lem3372608 _87647 P Q). Qed.
Lemma lem3372610 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term190 _87647 _87658 s x f t) = (term191 _87647 _87658 s x f t).
Proof. exact (@lem3372609 _87647 (term130 _87647 _87658 s x f t) (term185 _87647 _87658 s x f t)). Qed.
Lemma lem3372611 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term192 _87647 _87658 s x' f t x) = (term128 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term192 _87647 _87658 s x' f t x)). Qed.
Lemma lem3372612 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term193 _87647 _87658 s x f t) = (term130 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372611 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372613 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372614 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term194 _87647 _87658 s x f t) = (term131 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372613 _87647) (@lem3372612 _87647 _87658 s x f t)). Qed.
Lemma lem3372615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372616 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term195 _87647 _87658 s x f t) = (term132 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372615) (@lem3372614 _87647 _87658 s x f t)). Qed.
Lemma lem3372617 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term196 _87647 _87658 s x' f t x) = (term184 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term196 _87647 _87658 s x' f t x)). Qed.
Lemma lem3372618 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term197 _87647 _87658 s x f t) = (term185 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372617 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372619 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372620 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term198 _87647 _87658 s x f t) = (term186 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372619 _87647) (@lem3372618 _87647 _87658 s x f t)). Qed.
Lemma lem3372621 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term190 _87647 _87658 s x f t) = (term187 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372616 _87647 _87658 s x f t) (@lem3372620 _87647 _87658 s x f t)). Qed.
Lemma lem3372622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372623 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term199 _87647 _87658 s x f t) = (term200 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372622) (@lem3372621 _87647 _87658 s x f t)). Qed.
Lemma lem3372624 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term192 _87647 _87658 s x' f t x) = (term128 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term192 _87647 _87658 s x' f t x)). Qed.
Lemma lem3372625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372626 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term201 _87647 _87658 s x' f t x) = (term202 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372625) (@lem3372624 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372627 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term196 _87647 _87658 s x' f t x) = (term184 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term196 _87647 _87658 s x' f t x)). Qed.
Lemma lem3372628 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term203 _87647 _87658 s x' f t x) = (term204 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372626 _87647 _87658 x s x' f t) (@lem3372627 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372629 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term205 _87647 _87658 s x f t) = (term206 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372628 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372630 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372631 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term191 _87647 _87658 s x f t) = (term207 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372630 _87647) (@lem3372629 _87647 _87658 s x f t)). Qed.
Lemma lem3372632 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term190 _87647 _87658 s x f t) = (term191 _87647 _87658 s x f t)) = ((term187 _87647 _87658 s x f t) = (term207 _87647 _87658 s x f t)).
Proof. exact (MK_COMB (@lem3372623 _87647 _87658 s x f t) (@lem3372631 _87647 _87658 s x f t)). Qed.
Lemma lem3372633 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term187 _87647 _87658 s x f t) = (term207 _87647 _87658 s x f t).
Proof. exact (EQ_MP (@lem3372632 _87647 _87658 s x f t) (@lem3372610 _87647 _87658 s x f t)). Qed.
Lemma lem3372635 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3372636 {_87647 : Type'} (P : Prop) (Q : _87647 -> Prop) : (term208 _87647 P Q) = (term209 _87647 P Q).
Proof. exact (@lem3372635 _87647 P Q). Qed.
Lemma lem3372637 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term210 _87647 _87658 x s x' f t) = (term211 _87647 _87658 x s x' f t).
Proof. exact (@lem3372636 _87647 (term128 _87647 _87658 x s x' f t) (term183 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372638 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term212 _87647 _87658 x s x' f t x'') = (term181 _87647 _87658 x s x' f x'' t).
Proof. exact (eq_refl (term212 _87647 _87658 x s x' f t x'')). Qed.
Lemma lem3372639 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term213 _87647 _87658 x s x' f t) = (term183 _87647 _87658 x s x' f t).
Proof. exact (fun_ext (fun x'' : _87647 => @lem3372638 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372640 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372641 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term214 _87647 _87658 x s x' f t) = (term184 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372640 _87647) (@lem3372639 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372642 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term202 _87647 _87658 x s x' f t) = (term202 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term202 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372643 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term210 _87647 _87658 x s x' f t) = (term204 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372642 _87647 _87658 x s x' f t) (@lem3372641 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3372645 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term215 _87647 _87658 x s x' f t) = (term216 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372644) (@lem3372643 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372646 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term212 _87647 _87658 x s x' f t x'') = (term181 _87647 _87658 x s x' f x'' t).
Proof. exact (eq_refl (term212 _87647 _87658 x s x' f t x'')). Qed.
Lemma lem3372647 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term202 _87647 _87658 x s x' f t) = (term202 _87647 _87658 x s x' f t).
Proof. exact (eq_refl (term202 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372648 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term217 _87647 _87658 x s x' f t x'') = (term218 _87647 _87658 x s x' f x'' t).
Proof. exact (MK_COMB (@lem3372647 _87647 _87658 x s x' f t) (@lem3372646 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372649 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term219 _87647 _87658 x s x' f t) = (term220 _87647 _87658 x s x' f t).
Proof. exact (fun_ext (fun x'' : _87647 => @lem3372648 _87647 _87658 x s x' f x'' t)). Qed.
Lemma lem3372650 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372651 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term211 _87647 _87658 x s x' f t) = (term221 _87647 _87658 x s x' f t).
Proof. exact (MK_COMB (@lem3372650 _87647) (@lem3372649 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372652 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : ((term210 _87647 _87658 x s x' f t) = (term211 _87647 _87658 x s x' f t)) = ((term204 _87647 _87658 x s x' f t) = (term221 _87647 _87658 x s x' f t)).
Proof. exact (MK_COMB (@lem3372645 _87647 _87658 x s x' f t) (@lem3372651 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372653 {_87647 _87658 : Type'} (x : _87647) (s : _87647 -> Prop) (x' : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term204 _87647 _87658 x s x' f t) = (term221 _87647 _87658 x s x' f t).
Proof. exact (EQ_MP (@lem3372652 _87647 _87658 x s x' f t) (@lem3372637 _87647 _87658 x s x' f t)). Qed.
Lemma lem3372654 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term206 _87647 _87658 s x f t) = (term222 _87647 _87658 s x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372653 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372655 {_87647 : Type'} : (@ex _87647) = (@ex _87647).
Proof. exact (eq_refl (@ex _87647)). Qed.
Lemma lem3372656 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term207 _87647 _87658 s x f t) = (term223 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372655 _87647) (@lem3372654 _87647 _87658 s x f t)). Qed.
Lemma lem3372657 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term187 _87647 _87658 s x f t) = (term223 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372633 _87647 _87658 s x f t) (@lem3372656 _87647 _87658 s x f t)). Qed.
Lemma lem3372659 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term115 _87647 _87658 s x f t) = (term223 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372606 _87647 _87658 s x f t) (@lem3372657 _87647 _87658 s x f t)). Qed.
Lemma lem3372660 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term70 _87647 _87658 s x f t) = (term223 _87647 _87658 s x f t).
Proof. exact (TRANS (@lem3372195 _87647 _87658 s x f t) (@lem3372659 _87647 _87658 s x f t)). Qed.
Lemma lem3372661 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term70 _87647 _87658 s x f t) : term223 _87647 _87658 s x f t.
Proof. exact (EQ_MP (@lem3372660 _87647 _87658 s x f t) (@lem3372021 _87647 _87658 s x f t h1)). Qed.
Lemma lem3372662 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term221 _87647 _87658 x' s x f t) : term221 _87647 _87658 x' s x f t.
Proof. exact (h1). Qed.
Lemma lem3372663 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term218 _87647 _87658 x' s x f x'' t) : term218 _87647 _87658 x' s x f x'' t.
Proof. exact (h1). Qed.
Lemma lem3372682 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) (y : _87647) : (term71 _87647 _87658 f x y) = (term71 _87647 _87658 f x y).
Proof. exact (eq_refl (term71 _87647 _87658 f x y)). Qed.
Lemma lem3372683 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term72 _87647 _87658 f x) = (term72 _87647 _87658 f x).
Proof. exact (fun_ext (fun y : _87647 => @lem3372682 _87647 _87658 f x y)). Qed.
Lemma lem3372684 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372685 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term73 _87647 _87658 f x) = (term73 _87647 _87658 f x).
Proof. exact (MK_COMB (@lem3372684 _87647) (@lem3372683 _87647 _87658 f x)). Qed.
Lemma lem3372686 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term74 _87647 _87658 f) = (term74 _87647 _87658 f).
Proof. exact (fun_ext (fun x : _87647 => @lem3372685 _87647 _87658 f x)). Qed.
Lemma lem3372687 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372688 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term75 _87647 _87658 f) = (term75 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3372687 _87647) (@lem3372686 _87647 _87658 f)). Qed.
Lemma lem3372689 {_87647 _87658 : Type'} (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term75 _87647 _87658 f.
Proof. exact (EQ_MP (@lem3372688 _87647 _87658 f) (@lem3372091 _87647 _87658 f h1)). Qed.
Lemma lem3372722 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term154 _87647 _87658 x' s x f x'' t) = (term154 _87647 _87658 x' s x f x'' t).
Proof. exact (eq_refl (term154 _87647 _87658 x' s x f x'' t)). Qed.
Lemma lem3372751 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term80 _87647 _87658 x f s x' t) = (term80 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term80 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372752 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term89 _87647 _87658 x f s t) = (term89 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372751 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372753 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372754 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term90 _87647 _87658 x f s t) = (term90 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372753 _87647) (@lem3372752 _87647 _87658 x f s t)). Qed.
Lemma lem3372755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3372756 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term106 _87647 _87658 x f s t) = (term106 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372755) (@lem3372754 _87647 _87658 x f s t)). Qed.
Lemma lem3372757 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term181 _87647 _87658 x' s x f x'' t) = (term181 _87647 _87658 x' s x f x'' t).
Proof. exact (MK_COMB (@lem3372756 _87647 _87658 x f s t) (@lem3372722 _87647 _87658 x' s x f x'' t)). Qed.
Lemma lem3372776 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term92 _87647 _87658 x f x' t) = (term92 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term92 _87647 _87658 x f x' t)). Qed.
Lemma lem3372777 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term98 _87647 _87658 x f t) = (term98 _87647 _87658 x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372776 _87647 _87658 x f x' t)). Qed.
Lemma lem3372778 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372779 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term99 _87647 _87658 x f t) = (term99 _87647 _87658 x f t).
Proof. exact (MK_COMB (@lem3372778 _87647) (@lem3372777 _87647 _87658 x f t)). Qed.
Lemma lem3372798 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term92 _87647 _87658 x f x' s) = (term92 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term92 _87647 _87658 x f x' s)). Qed.
Lemma lem3372799 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term98 _87647 _87658 x f s) = (term98 _87647 _87658 x f s).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372798 _87647 _87658 x f x' s)). Qed.
Lemma lem3372800 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372801 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term99 _87647 _87658 x f s) = (term99 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372800 _87647) (@lem3372799 _87647 _87658 x f s)). Qed.
Lemma lem3372802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372803 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term101 _87647 _87658 x f s) = (term101 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372802) (@lem3372801 _87647 _87658 x f s)). Qed.
Lemma lem3372804 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term103 _87647 _87658 s x f t) = (term103 _87647 _87658 s x f t).
Proof. exact (MK_COMB (@lem3372803 _87647 _87658 x f s) (@lem3372779 _87647 _87658 x f t)). Qed.
Lemma lem3372829 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term126 _87647 _87658 x f s x' t) = (term126 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term126 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372830 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term128 _87647 _87658 x' s x f t) = (term128 _87647 _87658 x' s x f t).
Proof. exact (MK_COMB (@lem3372829 _87647 _87658 x f s x' t) (@lem3372804 _87647 _87658 s x f t)). Qed.
Lemma lem3372831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3372832 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term202 _87647 _87658 x' s x f t) = (term202 _87647 _87658 x' s x f t).
Proof. exact (MK_COMB (@lem3372831) (@lem3372830 _87647 _87658 x' s x f t)). Qed.
Lemma lem3372833 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) : (term218 _87647 _87658 x' s x f x'' t) = (term218 _87647 _87658 x' s x f x'' t).
Proof. exact (MK_COMB (@lem3372832 _87647 _87658 x' s x f t) (@lem3372757 _87647 _87658 x' s x f x'' t)). Qed.
Lemma lem3372834 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term218 _87647 _87658 x' s x f x'' t) : term218 _87647 _87658 x' s x f x'' t.
Proof. exact (EQ_MP (@lem3372833 _87647 _87658 x' s x f x'' t) (@lem3372663 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3372835 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term128 _87647 _87658 x' s x f t.
Proof. exact (h1). Qed.
Lemma lem3372836 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term181 _87647 _87658 x' s x f x'' t.
Proof. exact (h1). Qed.
Lemma lem3372837 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term103 _87647 _87658 s x f t.
Proof. exact (proj2 (@lem3372835 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3372838 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term25 _87647 _87658 x f s x' t.
Proof. exact (proj1 (@lem3372835 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3372839 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term6 _87647 s x' t.
Proof. exact (proj2 (@lem3372838 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3372843 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) : term99 _87647 _87658 x f s.
Proof. exact (h1). Qed.
Lemma lem3372844 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) : term99 _87647 _87658 x f t.
Proof. exact (h1). Qed.
Lemma lem3372845 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term154 _87647 _87658 x' s x f x'' t.
Proof. exact (proj2 (@lem3372836 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3372846 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term90 _87647 _87658 x f s t.
Proof. exact (proj1 (@lem3372836 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3372847 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term62 _87647 _87658 x f x'' t.
Proof. exact (proj2 (@lem3372845 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3372848 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term62 _87647 _87658 x f x' s.
Proof. exact (proj1 (@lem3372845 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3372888 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (s : _87647 -> Prop) : (term92 _87647 _87658 x f x' s) = (term92 _87647 _87658 x f x' s).
Proof. exact (eq_refl (term92 _87647 _87658 x f x' s)). Qed.
Lemma lem3372889 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term98 _87647 _87658 x f s) = (term98 _87647 _87658 x f s).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372888 _87647 _87658 x f x' s)). Qed.
Lemma lem3372890 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372892 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) : (term99 _87647 _87658 x f s) = (term99 _87647 _87658 x f s).
Proof. exact (MK_COMB (@lem3372890 _87647) (@lem3372889 _87647 _87658 x f s)). Qed.
Lemma lem3372893 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) : term99 _87647 _87658 x f s.
Proof. exact (EQ_MP (@lem3372892 _87647 _87658 x f s) (@lem3372843 _87647 _87658 x f s h1)). Qed.
Lemma lem3372929 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x' : _87647) (t : _87647 -> Prop) : (term92 _87647 _87658 x f x' t) = (term92 _87647 _87658 x f x' t).
Proof. exact (eq_refl (term92 _87647 _87658 x f x' t)). Qed.
Lemma lem3372930 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term98 _87647 _87658 x f t) = (term98 _87647 _87658 x f t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372929 _87647 _87658 x f x' t)). Qed.
Lemma lem3372931 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372933 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) : (term99 _87647 _87658 x f t) = (term99 _87647 _87658 x f t).
Proof. exact (MK_COMB (@lem3372931 _87647) (@lem3372930 _87647 _87658 x f t)). Qed.
Lemma lem3372934 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) : term99 _87647 _87658 x f t.
Proof. exact (EQ_MP (@lem3372933 _87647 _87658 x f t) (@lem3372844 _87647 _87658 x f t h1)). Qed.
Lemma lem3372942 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) (y : _87647) : (term71 _87647 _87658 f x y) = (term71 _87647 _87658 f x y).
Proof. exact (eq_refl (term71 _87647 _87658 f x y)). Qed.
Lemma lem3372943 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term72 _87647 _87658 f x) = (term72 _87647 _87658 f x).
Proof. exact (fun_ext (fun y : _87647 => @lem3372942 _87647 _87658 f x y)). Qed.
Lemma lem3372944 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372945 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x : _87647) : (term73 _87647 _87658 f x) = (term73 _87647 _87658 f x).
Proof. exact (MK_COMB (@lem3372944 _87647) (@lem3372943 _87647 _87658 f x)). Qed.
Lemma lem3372946 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term74 _87647 _87658 f) = (term74 _87647 _87658 f).
Proof. exact (fun_ext (fun x : _87647 => @lem3372945 _87647 _87658 f x)). Qed.
Lemma lem3372947 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372949 {_87647 _87658 : Type'} (f : _87647 -> _87658) : (term75 _87647 _87658 f) = (term75 _87647 _87658 f).
Proof. exact (MK_COMB (@lem3372947 _87647) (@lem3372946 _87647 _87658 f)). Qed.
Lemma lem3372950 {_87647 _87658 : Type'} (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term75 _87647 _87658 f.
Proof. exact (EQ_MP (@lem3372949 _87647 _87658 f) (@lem3372689 _87647 _87658 f h1)). Qed.
Lemma lem3372964 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (x' : _87647) (t : _87647 -> Prop) : (term80 _87647 _87658 x f s x' t) = (term80 _87647 _87658 x f s x' t).
Proof. exact (eq_refl (term80 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372965 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term89 _87647 _87658 x f s t) = (term89 _87647 _87658 x f s t).
Proof. exact (fun_ext (fun x' : _87647 => @lem3372964 _87647 _87658 x f s x' t)). Qed.
Lemma lem3372966 {_87647 : Type'} : (@all _87647) = (@all _87647).
Proof. exact (eq_refl (@all _87647)). Qed.
Lemma lem3372968 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (t : _87647 -> Prop) : (term90 _87647 _87658 x f s t) = (term90 _87647 _87658 x f s t).
Proof. exact (MK_COMB (@lem3372966 _87647) (@lem3372965 _87647 _87658 x f s t)). Qed.
Lemma lem3372969 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term90 _87647 _87658 x f s t.
Proof. exact (EQ_MP (@lem3372968 _87647 _87658 x f s t) (@lem3372846 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3372992 {_87647 _87658 : Type'} (_35262 : _87647) (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) : term224 _87647 _87658 x f s _35262.
Proof. exact (@lem3372893 _87647 _87658 x f s h1 _35262). Qed.
Lemma lem3372993 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term224 _87647 _87658 x f s _35262) = (term92 _87647 _87658 x f _35262 s).
Proof. exact (eq_refl (term224 _87647 _87658 x f s _35262)). Qed.
Lemma lem3373001 {_87647 _87658 : Type'} (_35265 : _87647) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) : term224 _87647 _87658 x f t _35265.
Proof. exact (@lem3372934 _87647 _87658 x f t h1 _35265). Qed.
Lemma lem3373002 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term224 _87647 _87658 x f t _35265) = (term92 _87647 _87658 x f _35265 t).
Proof. exact (eq_refl (term224 _87647 _87658 x f t _35265)). Qed.
Lemma lem3373004 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term225 _87647 _87658 f _35266.
Proof. exact (@lem3372950 _87647 _87658 f h1 _35266). Qed.
Lemma lem3373005 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35266 : _87647) : (term225 _87647 _87658 f _35266) = (term73 _87647 _87658 f _35266).
Proof. exact (eq_refl (term225 _87647 _87658 f _35266)). Qed.
Lemma lem3373006 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term73 _87647 _87658 f _35266.
Proof. exact (EQ_MP (@lem3373005 _87647 _87658 f _35266) (@lem3373004 _87647 _87658 _35266 f h1)). Qed.
Lemma lem3373007 {_87647 _87658 : Type'} (_35266 : _87647) (_35267 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term226 _87647 _87658 f _35266 _35267.
Proof. exact (@lem3373006 _87647 _87658 _35266 f h1 _35267). Qed.
Lemma lem3373008 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35266 : _87647) (_35267 : _87647) : (term226 _87647 _87658 f _35266 _35267) = (term71 _87647 _87658 f _35266 _35267).
Proof. exact (eq_refl (term226 _87647 _87658 f _35266 _35267)). Qed.
Lemma lem3373010 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term227 _87647 _87658 x f s t _35268.
Proof. exact (@lem3372969 _87647 _87658 x' s x f x'' t h1 _35268). Qed.
Lemma lem3373011 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term227 _87647 _87658 x f s t _35268) = (term80 _87647 _87658 x f s _35268 t).
Proof. exact (eq_refl (term227 _87647 _87658 x f s t _35268)). Qed.
Lemma lem3373020 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3372838 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373030 {_87647 _87658 : Type'} (_35262 : _87647) (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) : term92 _87647 _87658 x f _35262 s.
Proof. exact (EQ_MP (@lem3372993 _87647 _87658 x f _35262 s) (@lem3372992 _87647 _87658 _35262 x f s h1)). Qed.
Lemma lem3373038 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3372838 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373048 {_87647 _87658 : Type'} (_35265 : _87647) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) : term92 _87647 _87658 x f _35265 t.
Proof. exact (EQ_MP (@lem3373002 _87647 _87658 x f _35265 t) (@lem3373001 _87647 _87658 _35265 x f t h1)). Qed.
Lemma lem3373064 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term80 _87647 _87658 x f s _35268 t.
Proof. exact (EQ_MP (@lem3373011 _87647 _87658 x f s _35268 t) (@lem3373010 _87647 _87658 _35268 x' s x f x'' t h1)). Qed.
Lemma lem3373066 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : x = (f x'').
Proof. exact (proj1 (@lem3372847 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373070 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : x = (f x').
Proof. exact (proj1 (@lem3372848 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373129 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term228 _87647 _87658 f _35262 s) = (term228 _87647 _87658 f _35262 s).
Proof. exact (eq_refl (term228 _87647 _87658 f _35262 s)). Qed.
Lemma lem3373130 {_87647 _87658 : Type'} (_35262 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : (term229 _87647 _87658 f _35262 s x) = (term230 _87647 _87658 _35262 s f x').
Proof. exact (MK_COMB (@lem3373129 _87647 _87658 f _35262 s) (@lem3373020 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373131 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term230 _87647 _87658 _35262 s f x') = (term231 _87647 _87658 x' f _35262 s).
Proof. exact (eq_refl (term230 _87647 _87658 _35262 s f x')). Qed.
Lemma lem3373132 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) (x : _87658) : (term232 _87647 _87658 f _35262 s x) = (term232 _87647 _87658 f _35262 s x).
Proof. exact (eq_refl (term232 _87647 _87658 f _35262 s x)). Qed.
Lemma lem3373133 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : ((term229 _87647 _87658 f _35262 s x) = (term230 _87647 _87658 _35262 s f x')) = ((term229 _87647 _87658 f _35262 s x) = (term231 _87647 _87658 x' f _35262 s)).
Proof. exact (MK_COMB (@lem3373132 _87647 _87658 f _35262 s x) (@lem3373131 _87647 _87658 x' f _35262 s)). Qed.
Lemma lem3373134 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term229 _87647 _87658 f _35262 s x) = (term92 _87647 _87658 x f _35262 s).
Proof. exact (eq_refl (term229 _87647 _87658 f _35262 s x)). Qed.
Lemma lem3373135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3373136 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term232 _87647 _87658 f _35262 s x) = (term233 _87647 _87658 x f _35262 s).
Proof. exact (MK_COMB (@lem3373135) (@lem3373134 _87647 _87658 x f _35262 s)). Qed.
Lemma lem3373137 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term231 _87647 _87658 x' f _35262 s) = (term231 _87647 _87658 x' f _35262 s).
Proof. exact (eq_refl (term231 _87647 _87658 x' f _35262 s)). Qed.
Lemma lem3373138 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : ((term229 _87647 _87658 f _35262 s x) = (term231 _87647 _87658 x' f _35262 s)) = ((term92 _87647 _87658 x f _35262 s) = (term231 _87647 _87658 x' f _35262 s)).
Proof. exact (MK_COMB (@lem3373136 _87647 _87658 x f _35262 s) (@lem3373137 _87647 _87658 x' f _35262 s)). Qed.
Lemma lem3373139 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : ((term229 _87647 _87658 f _35262 s x) = (term230 _87647 _87658 _35262 s f x')) = ((term92 _87647 _87658 x f _35262 s) = (term231 _87647 _87658 x' f _35262 s)).
Proof. exact (TRANS (@lem3373133 _87647 _87658 x x' f _35262 s) (@lem3373138 _87647 _87658 x x' f _35262 s)). Qed.
Lemma lem3373140 {_87647 _87658 : Type'} (_35262 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : (term92 _87647 _87658 x f _35262 s) = (term231 _87647 _87658 x' f _35262 s).
Proof. exact (EQ_MP (@lem3373139 _87647 _87658 x x' f _35262 s) (@lem3373130 _87647 _87658 _35262 x' s x f t h1)). Qed.
Lemma lem3373141 {_87647 _87658 : Type'} (_35262 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : term231 _87647 _87658 x' f _35262 s.
Proof. exact (EQ_MP (@lem3373140 _87647 _87658 _35262 x' s x f t h2) (@lem3373030 _87647 _87658 _35262 x f s h1)). Qed.
Lemma lem3373198 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term228 _87647 _87658 f _35265 t) = (term228 _87647 _87658 f _35265 t).
Proof. exact (eq_refl (term228 _87647 _87658 f _35265 t)). Qed.
Lemma lem3373199 {_87647 _87658 : Type'} (_35265 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : (term229 _87647 _87658 f _35265 t x) = (term230 _87647 _87658 _35265 t f x').
Proof. exact (MK_COMB (@lem3373198 _87647 _87658 f _35265 t) (@lem3373038 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373200 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term230 _87647 _87658 _35265 t f x') = (term231 _87647 _87658 x' f _35265 t).
Proof. exact (eq_refl (term230 _87647 _87658 _35265 t f x')). Qed.
Lemma lem3373201 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) (x : _87658) : (term232 _87647 _87658 f _35265 t x) = (term232 _87647 _87658 f _35265 t x).
Proof. exact (eq_refl (term232 _87647 _87658 f _35265 t x)). Qed.
Lemma lem3373202 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : ((term229 _87647 _87658 f _35265 t x) = (term230 _87647 _87658 _35265 t f x')) = ((term229 _87647 _87658 f _35265 t x) = (term231 _87647 _87658 x' f _35265 t)).
Proof. exact (MK_COMB (@lem3373201 _87647 _87658 f _35265 t x) (@lem3373200 _87647 _87658 x' f _35265 t)). Qed.
Lemma lem3373203 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term229 _87647 _87658 f _35265 t x) = (term92 _87647 _87658 x f _35265 t).
Proof. exact (eq_refl (term229 _87647 _87658 f _35265 t x)). Qed.
Lemma lem3373204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3373205 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term232 _87647 _87658 f _35265 t x) = (term233 _87647 _87658 x f _35265 t).
Proof. exact (MK_COMB (@lem3373204) (@lem3373203 _87647 _87658 x f _35265 t)). Qed.
Lemma lem3373206 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term231 _87647 _87658 x' f _35265 t) = (term231 _87647 _87658 x' f _35265 t).
Proof. exact (eq_refl (term231 _87647 _87658 x' f _35265 t)). Qed.
Lemma lem3373207 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : ((term229 _87647 _87658 f _35265 t x) = (term231 _87647 _87658 x' f _35265 t)) = ((term92 _87647 _87658 x f _35265 t) = (term231 _87647 _87658 x' f _35265 t)).
Proof. exact (MK_COMB (@lem3373205 _87647 _87658 x f _35265 t) (@lem3373206 _87647 _87658 x' f _35265 t)). Qed.
Lemma lem3373208 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : ((term229 _87647 _87658 f _35265 t x) = (term230 _87647 _87658 _35265 t f x')) = ((term92 _87647 _87658 x f _35265 t) = (term231 _87647 _87658 x' f _35265 t)).
Proof. exact (TRANS (@lem3373202 _87647 _87658 x x' f _35265 t) (@lem3373207 _87647 _87658 x x' f _35265 t)). Qed.
Lemma lem3373209 {_87647 _87658 : Type'} (_35265 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : (term92 _87647 _87658 x f _35265 t) = (term231 _87647 _87658 x' f _35265 t).
Proof. exact (EQ_MP (@lem3373208 _87647 _87658 x x' f _35265 t) (@lem3373199 _87647 _87658 _35265 x' s x f t h1)). Qed.
Lemma lem3373210 {_87647 _87658 : Type'} (_35265 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : term231 _87647 _87658 x' f _35265 t.
Proof. exact (EQ_MP (@lem3373209 _87647 _87658 _35265 x' s x f t h2) (@lem3373048 _87647 _87658 _35265 x f t h1)). Qed.
Lemma lem3373238 {_87647 _87658 : Type'} (_35266 : _87647) (_35267 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term71 _87647 _87658 f _35266 _35267.
Proof. exact (EQ_MP (@lem3373008 _87647 _87658 f _35266 _35267) (@lem3373007 _87647 _87658 _35266 _35267 f h1)). Qed.
Lemma lem3373239 {_87647 _87658 : Type'} (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term234 _87647 _87658 f s _35268 t) = (term234 _87647 _87658 f s _35268 t).
Proof. exact (eq_refl (term234 _87647 _87658 f s _35268 t)). Qed.
Lemma lem3373240 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (term235 _87647 _87658 f s _35268 t x) = (term236 _87647 _87658 s _35268 t f x').
Proof. exact (MK_COMB (@lem3373239 _87647 _87658 f s _35268 t) (@lem3373070 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373241 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term236 _87647 _87658 s _35268 t f x') = (term237 _87647 _87658 x' f s _35268 t).
Proof. exact (eq_refl (term236 _87647 _87658 s _35268 t f x')). Qed.
Lemma lem3373242 {_87647 _87658 : Type'} (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) (x : _87658) : (term238 _87647 _87658 f s _35268 t x) = (term238 _87647 _87658 f s _35268 t x).
Proof. exact (eq_refl (term238 _87647 _87658 f s _35268 t x)). Qed.
Lemma lem3373243 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : ((term235 _87647 _87658 f s _35268 t x) = (term236 _87647 _87658 s _35268 t f x')) = ((term235 _87647 _87658 f s _35268 t x) = (term237 _87647 _87658 x' f s _35268 t)).
Proof. exact (MK_COMB (@lem3373242 _87647 _87658 f s _35268 t x) (@lem3373241 _87647 _87658 x' f s _35268 t)). Qed.
Lemma lem3373244 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term235 _87647 _87658 f s _35268 t x) = (term80 _87647 _87658 x f s _35268 t).
Proof. exact (eq_refl (term235 _87647 _87658 f s _35268 t x)). Qed.
Lemma lem3373245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3373246 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term238 _87647 _87658 f s _35268 t x) = (term239 _87647 _87658 x f s _35268 t).
Proof. exact (MK_COMB (@lem3373245) (@lem3373244 _87647 _87658 x f s _35268 t)). Qed.
Lemma lem3373247 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term237 _87647 _87658 x' f s _35268 t) = (term237 _87647 _87658 x' f s _35268 t).
Proof. exact (eq_refl (term237 _87647 _87658 x' f s _35268 t)). Qed.
Lemma lem3373248 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : ((term235 _87647 _87658 f s _35268 t x) = (term237 _87647 _87658 x' f s _35268 t)) = ((term80 _87647 _87658 x f s _35268 t) = (term237 _87647 _87658 x' f s _35268 t)).
Proof. exact (MK_COMB (@lem3373246 _87647 _87658 x f s _35268 t) (@lem3373247 _87647 _87658 x' f s _35268 t)). Qed.
Lemma lem3373249 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : ((term235 _87647 _87658 f s _35268 t x) = (term236 _87647 _87658 s _35268 t f x')) = ((term80 _87647 _87658 x f s _35268 t) = (term237 _87647 _87658 x' f s _35268 t)).
Proof. exact (TRANS (@lem3373243 _87647 _87658 x x' f s _35268 t) (@lem3373248 _87647 _87658 x x' f s _35268 t)). Qed.
Lemma lem3373250 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (term80 _87647 _87658 x f s _35268 t) = (term237 _87647 _87658 x' f s _35268 t).
Proof. exact (EQ_MP (@lem3373249 _87647 _87658 x x' f s _35268 t) (@lem3373240 _87647 _87658 _35268 x' s x f x'' t h1)). Qed.
Lemma lem3373251 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term237 _87647 _87658 x' f s _35268 t.
Proof. exact (EQ_MP (@lem3373250 _87647 _87658 _35268 x' s x f x'' t h1) (@lem3373064 _87647 _87658 _35268 x' s x f x'' t h1)). Qed.
Lemma lem3373252 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x'' : _87647) : (term240 _87647 _87658 f x'') = (term240 _87647 _87658 f x'').
Proof. exact (eq_refl (term240 _87647 _87658 f x'')). Qed.
Lemma lem3373253 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (term241 _87647 _87658 f x'' x) = (term242 _87647 _87658 x'' f x').
Proof. exact (MK_COMB (@lem3373252 _87647 _87658 f x'') (@lem3373070 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373254 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : (term242 _87647 _87658 x'' f x') = ((f x') = (f x'')).
Proof. exact (eq_refl (term242 _87647 _87658 x'' f x')). Qed.
Lemma lem3373255 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x'' : _87647) (x : _87658) : (term243 _87647 _87658 f x'' x) = (term243 _87647 _87658 f x'' x).
Proof. exact (eq_refl (term243 _87647 _87658 f x'' x)). Qed.
Lemma lem3373256 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : ((term241 _87647 _87658 f x'' x) = (term242 _87647 _87658 x'' f x')) = ((term241 _87647 _87658 f x'' x) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3373255 _87647 _87658 f x'' x) (@lem3373254 _87647 _87658 x' f x'')). Qed.
Lemma lem3373257 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x'' : _87647) : (term241 _87647 _87658 f x'' x) = (x = (f x'')).
Proof. exact (eq_refl (term241 _87647 _87658 f x'' x)). Qed.
Lemma lem3373258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3373259 {_87647 _87658 : Type'} (x : _87658) (f : _87647 -> _87658) (x'' : _87647) : (term243 _87647 _87658 f x'' x) = (term244 _87647 _87658 x f x'').
Proof. exact (MK_COMB (@lem3373258) (@lem3373257 _87647 _87658 x f x'')). Qed.
Lemma lem3373260 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : ((f x') = (f x'')) = ((f x') = (f x'')).
Proof. exact (eq_refl ((f x') = (f x''))). Qed.
Lemma lem3373261 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : ((term241 _87647 _87658 f x'' x) = ((f x') = (f x''))) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (MK_COMB (@lem3373259 _87647 _87658 x f x'') (@lem3373260 _87647 _87658 x' f x'')). Qed.
Lemma lem3373262 {_87647 _87658 : Type'} (x : _87658) (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : ((term241 _87647 _87658 f x'' x) = (term242 _87647 _87658 x'' f x')) = ((x = (f x'')) = ((f x') = (f x''))).
Proof. exact (TRANS (@lem3373256 _87647 _87658 x x' f x'') (@lem3373261 _87647 _87658 x x' f x'')). Qed.
Lemma lem3373263 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (x = (f x'')) = ((f x') = (f x'')).
Proof. exact (EQ_MP (@lem3373262 _87647 _87658 x x' f x'') (@lem3373253 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373327 {_87658 : Type'} (x : _87658) : x = x.
Proof. exact (@lem21386 _87658 x). Qed.
Lemma lem3373328 {_87658 : Type'} (x : _87658) : x = x.
Proof. exact (@lem3373327 _87658 x). Qed.
Lemma lem3373329 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : (f x') = (f x').
Proof. exact (@lem3373328 _87658 (f x')). Qed.
Lemma lem3373330 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : term245 _87647 _87658 f x'.
Proof. exact (fun h0 : term246 _87647 _87658 f x' => @lem3373329 _87647 _87658 f x'). Qed.
Lemma lem3373332 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373333 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : (term245 _87647 _87658 f x') = ((f x') = (f x')).
Proof. exact (@lem3373332 ((f x') = (f x'))). Qed.
Lemma lem3373334 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3373333 _87647 _87658 f x') (@lem3373330 _87647 _87658 f x')). Qed.
Lemma lem3373336 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : @IN _87647 x' s.
Proof. exact (proj1 (@lem3372839 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373337 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term248 _87647 x' s.
Proof. exact (fun h0 : term249 _87647 x' s => @lem3373336 _87647 _87658 x' s x f t h1). Qed.
Lemma lem3373339 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373340 {_87647 : Type'} (x' : _87647) (s : _87647 -> Prop) : (term248 _87647 x' s) = (@IN _87647 x' s).
Proof. exact (@lem3373339 (@IN _87647 x' s)). Qed.
Lemma lem3373341 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : @IN _87647 x' s.
Proof. exact (EQ_MP (@lem3373340 _87647 x' s) (@lem3373337 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373343 (a : Prop) (b : Prop) : (term250 a b) = (term251 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3373344 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term231 _87647 _87658 x' f _35262 s) = (term252 _87647 _87658 x' f _35262 s).
Proof. exact (@lem3373343 ((f x') = (f _35262)) (@IN _87647 _35262 s)). Qed.
Lemma lem3373346 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3373347 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term252 _87647 _87658 x' f _35262 s) = (term253 _87647 _87658 x' f _35262 s).
Proof. exact (@lem3373346 (term254 _87647 _87658 x' f _35262 s)). Qed.
Lemma lem3373348 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35262 : _87647) (s : _87647 -> Prop) : (term231 _87647 _87658 x' f _35262 s) = (term253 _87647 _87658 x' f _35262 s).
Proof. exact (TRANS (@lem3373344 _87647 _87658 x' f _35262 s) (@lem3373347 _87647 _87658 x' f _35262 s)). Qed.
Lemma lem3373350 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term255 _87647 _87658 f x' s.
Proof. exact (conj (@lem3373334 _87647 _87658 f x') (@lem3373341 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373352 {_87647 _87658 : Type'} (_35262 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : term253 _87647 _87658 x' f _35262 s.
Proof. exact (EQ_MP (@lem3373348 _87647 _87658 x' f _35262 s) (@lem3373141 _87647 _87658 _35262 x' s x f t h1 h2)). Qed.
Lemma lem3373353 {_87647 _87658 : Type'} (_35262 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : term253 _87647 _87658 x' f _35262 s.
Proof. exact (@lem3373352 _87647 _87658 _35262 x' s x f t h1 h2). Qed.
Lemma lem3373354 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : term256 _87647 _87658 f x' s.
Proof. exact (@lem3373353 _87647 _87658 x' x' s x f t h1 h2). Qed.
Lemma lem3373357 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (@lem3373354 _87647 _87658 x' s x f t h1 h2 (@lem3373350 _87647 _87658 x' s x f t h2)). Qed.
Lemma lem3373358 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : term257.
Proof. exact (fun h0 : ~ False => @lem3373357 _87647 _87658 x' s x f t h1 h2). Qed.
Lemma lem3373360 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373361 : term257 = False.
Proof. exact (@lem3373360 False). Qed.
Lemma lem3373397 {_87658 : Type'} (x : _87658) : x = x.
Proof. exact (@lem21386 _87658 x). Qed.
Lemma lem3373398 {_87658 : Type'} (x : _87658) : x = x.
Proof. exact (@lem3373397 _87658 x). Qed.
Lemma lem3373399 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : (f x') = (f x').
Proof. exact (@lem3373398 _87658 (f x')). Qed.
Lemma lem3373400 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : term245 _87647 _87658 f x'.
Proof. exact (fun h0 : term246 _87647 _87658 f x' => @lem3373399 _87647 _87658 f x'). Qed.
Lemma lem3373402 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373403 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : (term245 _87647 _87658 f x') = ((f x') = (f x')).
Proof. exact (@lem3373402 ((f x') = (f x'))). Qed.
Lemma lem3373404 {_87647 _87658 : Type'} (f : _87647 -> _87658) (x' : _87647) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3373403 _87647 _87658 f x') (@lem3373400 _87647 _87658 f x')). Qed.
Lemma lem3373406 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : @IN _87647 x' t.
Proof. exact (proj2 (@lem3372839 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373407 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term248 _87647 x' t.
Proof. exact (fun h0 : term249 _87647 x' t => @lem3373406 _87647 _87658 x' s x f t h1). Qed.
Lemma lem3373409 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373410 {_87647 : Type'} (x' : _87647) (t : _87647 -> Prop) : (term248 _87647 x' t) = (@IN _87647 x' t).
Proof. exact (@lem3373409 (@IN _87647 x' t)). Qed.
Lemma lem3373411 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : @IN _87647 x' t.
Proof. exact (EQ_MP (@lem3373410 _87647 x' t) (@lem3373407 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373413 (a : Prop) (b : Prop) : (term250 a b) = (term251 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3373414 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term231 _87647 _87658 x' f _35265 t) = (term252 _87647 _87658 x' f _35265 t).
Proof. exact (@lem3373413 ((f x') = (f _35265)) (@IN _87647 _35265 t)). Qed.
Lemma lem3373416 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3373417 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term252 _87647 _87658 x' f _35265 t) = (term253 _87647 _87658 x' f _35265 t).
Proof. exact (@lem3373416 (term254 _87647 _87658 x' f _35265 t)). Qed.
Lemma lem3373418 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35265 : _87647) (t : _87647 -> Prop) : (term231 _87647 _87658 x' f _35265 t) = (term253 _87647 _87658 x' f _35265 t).
Proof. exact (TRANS (@lem3373414 _87647 _87658 x' f _35265 t) (@lem3373417 _87647 _87658 x' f _35265 t)). Qed.
Lemma lem3373420 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : term255 _87647 _87658 f x' t.
Proof. exact (conj (@lem3373404 _87647 _87658 f x') (@lem3373411 _87647 _87658 x' s x f t h1)). Qed.
Lemma lem3373422 {_87647 _87658 : Type'} (_35265 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : term253 _87647 _87658 x' f _35265 t.
Proof. exact (EQ_MP (@lem3373418 _87647 _87658 x' f _35265 t) (@lem3373210 _87647 _87658 _35265 x' s x f t h1 h2)). Qed.
Lemma lem3373423 {_87647 _87658 : Type'} (_35265 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : term253 _87647 _87658 x' f _35265 t.
Proof. exact (@lem3373422 _87647 _87658 _35265 x' s x f t h1 h2). Qed.
Lemma lem3373424 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : term256 _87647 _87658 f x' t.
Proof. exact (@lem3373423 _87647 _87658 x' x' s x f t h1 h2). Qed.
Lemma lem3373427 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (@lem3373424 _87647 _87658 x' s x f t h1 h2 (@lem3373420 _87647 _87658 x' s x f t h2)). Qed.
Lemma lem3373428 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : term257.
Proof. exact (fun h0 : ~ False => @lem3373427 _87647 _87658 x' s x f t h1 h2). Qed.
Lemma lem3373430 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373431 : term257 = False.
Proof. exact (@lem3373430 False). Qed.
Lemma lem3373433 {_87647 : Type'} : (@IN _87647) = (@IN _87647).
Proof. exact (eq_refl (@IN _87647)). Qed.
Lemma lem3373434 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) (h1 : _35313 = _35315) : _35313 = _35315.
Proof. exact (h1). Qed.
Lemma lem3373435 {_87647 : Type'} (_35314 : _87647 -> Prop) (_35316 : _87647 -> Prop) (h1 : _35314 = _35316) : _35314 = _35316.
Proof. exact (h1). Qed.
Lemma lem3373436 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) (h1 : _35313 = _35315) : (@IN _87647 _35313) = (@IN _87647 _35315).
Proof. exact (MK_COMB (@lem3373433 _87647) (@lem3373434 _87647 _35313 _35315 h1)). Qed.
Lemma lem3373437 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) (_35314 : _87647 -> Prop) (_35316 : _87647 -> Prop) (h1 : _35313 = _35315) (h2 : _35314 = _35316) : (@IN _87647 _35313 _35314) = (@IN _87647 _35315 _35316).
Proof. exact (MK_COMB (@lem3373436 _87647 _35313 _35315 h1) (@lem3373435 _87647 _35314 _35316 h2)). Qed.
Lemma lem3373439 (b : Prop) (a : Prop) : term258 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3373440 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : term259 _87647 _35315 _35316 _35313 _35314.
Proof. exact (@lem3373439 (@IN _87647 _35315 _35316) (@IN _87647 _35313 _35314)). Qed.
Lemma lem3373441 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) (_35314 : _87647 -> Prop) (_35316 : _87647 -> Prop) (h1 : _35313 = _35315) (h2 : _35314 = _35316) : term260 _87647 _35315 _35316 _35313 _35314.
Proof. exact (@lem3373440 _87647 _35315 _35316 _35313 _35314 (@lem3373437 _87647 _35313 _35315 _35314 _35316 h1 h2)). Qed.
Lemma lem3373442 {_87647 : Type'} (_35316 : _87647 -> Prop) (_35314 : _87647 -> Prop) (_35313 : _87647) (_35315 : _87647) (h1 : _35313 = _35315) : term261 _87647 _35315 _35316 _35313 _35314.
Proof. exact (fun h0 : _35314 = _35316 => @lem3373441 _87647 _35313 _35315 _35314 _35316 h1 h0). Qed.
Lemma lem3373444 (a : Prop) (b : Prop) : (a -> b) = (term262 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3373445 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term261 _87647 _35315 _35316 _35313 _35314) = (term263 _87647 _35315 _35316 _35313 _35314).
Proof. exact (@lem3373444 (_35314 = _35316) (term260 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373446 {_87647 : Type'} (_35316 : _87647 -> Prop) (_35314 : _87647 -> Prop) (_35313 : _87647) (_35315 : _87647) (h1 : _35313 = _35315) : term263 _87647 _35315 _35316 _35313 _35314.
Proof. exact (EQ_MP (@lem3373445 _87647 _35315 _35316 _35313 _35314) (@lem3373442 _87647 _35316 _35314 _35313 _35315 h1)). Qed.
Lemma lem3373447 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : term264 _87647 _35315 _35316 _35313 _35314.
Proof. exact (fun h0 : _35313 = _35315 => @lem3373446 _87647 _35316 _35314 _35313 _35315 h0). Qed.
Lemma lem3373449 (a : Prop) (b : Prop) : (a -> b) = (term262 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3373450 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term264 _87647 _35315 _35316 _35313 _35314) = (term265 _87647 _35315 _35316 _35313 _35314).
Proof. exact (@lem3373449 (_35313 = _35315) (term263 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373451 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : term265 _87647 _35315 _35316 _35313 _35314.
Proof. exact (EQ_MP (@lem3373450 _87647 _35315 _35316 _35313 _35314) (@lem3373447 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373467 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3373263 _87647 _87658 x' s x f x'' t h1) (@lem3373066 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373468 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term266 _87647 _87658 x' f x''.
Proof. exact (fun h0 : term267 _87647 _87658 x' f x'' => @lem3373467 _87647 _87658 x' s x f x'' t h1). Qed.
Lemma lem3373470 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373471 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : (term266 _87647 _87658 x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3373470 ((f x') = (f x''))). Qed.
Lemma lem3373472 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3373471 _87647 _87658 x' f x'') (@lem3373468 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373474 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3373263 _87647 _87658 x' s x f x'' t h1) (@lem3373066 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373475 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term266 _87647 _87658 x' f x''.
Proof. exact (fun h0 : term267 _87647 _87658 x' f x'' => @lem3373474 _87647 _87658 x' s x f x'' t h1). Qed.
Lemma lem3373477 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373478 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (x'' : _87647) : (term266 _87647 _87658 x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3373477 ((f x') = (f x''))). Qed.
Lemma lem3373479 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3373478 _87647 _87658 x' f x'') (@lem3373475 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373485 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3373486 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : (term71 _87647 _87658 f _35266 _35267) = (term268 _87647 _87658 _35266 f _35267).
Proof. exact (@lem3373485 (_35266 = _35267) (term267 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3373497 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : (term269 _87647 _87658 f _35266 _35267) = (term270 _87647 _87658 _35266 f _35267).
Proof. exact (MK_COMB (@lem3373496) (@lem3373486 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373507 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : (term268 _87647 _87658 _35266 f _35267) = (term268 _87647 _87658 _35266 f _35267).
Proof. exact (eq_refl (term268 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373508 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : ((term71 _87647 _87658 f _35266 _35267) = (term268 _87647 _87658 _35266 f _35267)) = ((term268 _87647 _87658 _35266 f _35267) = (term268 _87647 _87658 _35266 f _35267)).
Proof. exact (MK_COMB (@lem3373497 _87647 _87658 _35266 f _35267) (@lem3373507 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373510 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3373511 (x : Prop) : (x = x) = True.
Proof. exact (@lem3373510 Prop x). Qed.
Lemma lem3373512 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : ((term268 _87647 _87658 _35266 f _35267) = (term268 _87647 _87658 _35266 f _35267)) = True.
Proof. exact (@lem3373511 (term268 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373513 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : ((term71 _87647 _87658 f _35266 _35267) = (term268 _87647 _87658 _35266 f _35267)) = True.
Proof. exact (TRANS (@lem3373508 _87647 _87658 _35266 f _35267) (@lem3373512 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373514 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : True = ((term71 _87647 _87658 f _35266 _35267) = (term268 _87647 _87658 _35266 f _35267)).
Proof. exact (SYM (@lem3373513 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373515 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : (term71 _87647 _87658 f _35266 _35267) = (term268 _87647 _87658 _35266 f _35267).
Proof. exact (EQ_MP (@lem3373514 _87647 _87658 _35266 f _35267) (@lem0)). Qed.
Lemma lem3373516 {_87647 _87658 : Type'} (_35266 : _87647) (_35267 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term268 _87647 _87658 _35266 f _35267.
Proof. exact (EQ_MP (@lem3373515 _87647 _87658 _35266 f _35267) (@lem3373238 _87647 _87658 _35266 _35267 f h1)). Qed.
Lemma lem3373518 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3373519 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35266 : _87647) (_35267 : _87647) : (term268 _87647 _87658 _35266 f _35267) = (term272 _87647 _87658 f _35266 _35267).
Proof. exact (@lem3373518 (term267 _87647 _87658 _35266 f _35267) (_35266 = _35267)). Qed.
Lemma lem3373521 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3373522 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : (term273 _87647 _87658 _35266 f _35267) = ((f _35266) = (f _35267)).
Proof. exact (@lem3373521 ((f _35266) = (f _35267))). Qed.
Lemma lem3373523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3373524 {_87647 _87658 : Type'} (_35266 : _87647) (f : _87647 -> _87658) (_35267 : _87647) : (term274 _87647 _87658 _35266 f _35267) = (term275 _87647 _87658 _35266 f _35267).
Proof. exact (MK_COMB (@lem3373523) (@lem3373522 _87647 _87658 _35266 f _35267)). Qed.
Lemma lem3373525 {_87647 : Type'} (_35266 : _87647) (_35267 : _87647) : (_35266 = _35267) = (_35266 = _35267).
Proof. exact (eq_refl (_35266 = _35267)). Qed.
Lemma lem3373526 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35266 : _87647) (_35267 : _87647) : (term272 _87647 _87658 f _35266 _35267) = (term64 _87647 _87658 f _35266 _35267).
Proof. exact (MK_COMB (@lem3373524 _87647 _87658 _35266 f _35267) (@lem3373525 _87647 _35266 _35267)). Qed.
Lemma lem3373527 {_87647 _87658 : Type'} (f : _87647 -> _87658) (_35266 : _87647) (_35267 : _87647) : (term268 _87647 _87658 _35266 f _35267) = (term64 _87647 _87658 f _35266 _35267).
Proof. exact (TRANS (@lem3373519 _87647 _87658 f _35266 _35267) (@lem3373526 _87647 _87658 f _35266 _35267)). Qed.
Lemma lem3373530 {_87647 _87658 : Type'} (_35266 : _87647) (_35267 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term64 _87647 _87658 f _35266 _35267.
Proof. exact (EQ_MP (@lem3373527 _87647 _87658 f _35266 _35267) (@lem3373516 _87647 _87658 _35266 _35267 f h1)). Qed.
Lemma lem3373531 {_87647 _87658 : Type'} (_35266 : _87647) (_35267 : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term64 _87647 _87658 f _35266 _35267.
Proof. exact (@lem3373530 _87647 _87658 _35266 _35267 f h1). Qed.
Lemma lem3373532 {_87647 _87658 : Type'} (x' : _87647) (x'' : _87647) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term64 _87647 _87658 f x' x''.
Proof. exact (@lem3373531 _87647 _87658 x' x'' f h1). Qed.
Lemma lem3373535 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : x' = x''.
Proof. exact (@lem3373532 _87647 _87658 x' x'' f h1 (@lem3373479 _87647 _87658 x' s x f x'' t h2)). Qed.
Lemma lem3373536 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : term276 _87647 x' x''.
Proof. exact (fun h0 : term277 _87647 x' x'' => @lem3373535 _87647 _87658 x' s x f x'' t h1 h2). Qed.
Lemma lem3373538 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373539 {_87647 : Type'} (x' : _87647) (x'' : _87647) : (term276 _87647 x' x'') = (x' = x'').
Proof. exact (@lem3373538 (x' = x'')). Qed.
Lemma lem3373540 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : x' = x''.
Proof. exact (EQ_MP (@lem3373539 _87647 x' x'') (@lem3373536 _87647 _87658 x' s x f x'' t h1 h2)). Qed.
Lemma lem3373542 {_87647 : Type'} (x : _87647 -> Prop) : x = x.
Proof. exact (@lem21386 (_87647 -> Prop) x). Qed.
Lemma lem3373543 {_87647 : Type'} (x : _87647 -> Prop) : x = x.
Proof. exact (@lem3373542 _87647 x). Qed.
Lemma lem3373544 {_87647 : Type'} (s : _87647 -> Prop) : s = s.
Proof. exact (@lem3373543 _87647 s). Qed.
Lemma lem3373545 {_87647 : Type'} (s : _87647 -> Prop) : term278 _87647 s.
Proof. exact (fun h0 : term279 _87647 s => @lem3373544 _87647 s). Qed.
Lemma lem3373547 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373548 {_87647 : Type'} (s : _87647 -> Prop) : (term278 _87647 s) = (s = s).
Proof. exact (@lem3373547 (s = s)). Qed.
Lemma lem3373549 {_87647 : Type'} (s : _87647 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3373548 _87647 s) (@lem3373545 _87647 s)). Qed.
Lemma lem3373551 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : @IN _87647 x' s.
Proof. exact (proj2 (@lem3372848 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373552 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term248 _87647 x' s.
Proof. exact (fun h0 : term249 _87647 x' s => @lem3373551 _87647 _87658 x' s x f x'' t h1). Qed.
Lemma lem3373554 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373555 {_87647 : Type'} (x' : _87647) (s : _87647 -> Prop) : (term248 _87647 x' s) = (@IN _87647 x' s).
Proof. exact (@lem3373554 (@IN _87647 x' s)). Qed.
Lemma lem3373556 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : @IN _87647 x' s.
Proof. exact (EQ_MP (@lem3373555 _87647 x' s) (@lem3373552 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373574 (q : Prop) (p : Prop) (r : Prop) : (term280 p q r) = (term280 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3373575 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term263 _87647 _35315 _35316 _35313 _35314) = (term281 _87647 _35315 _35316 _35313 _35314).
Proof. exact (@lem3373574 (@IN _87647 _35315 _35316) (term282 _87647 _35314 _35316) (term249 _87647 _35313 _35314)). Qed.
Lemma lem3373593 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) : (term283 _87647 _35313 _35315) = (term283 _87647 _35313 _35315).
Proof. exact (eq_refl (term283 _87647 _35313 _35315)). Qed.
Lemma lem3373594 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term265 _87647 _35315 _35316 _35313 _35314) = (term284 _87647 _35315 _35316 _35313 _35314).
Proof. exact (MK_COMB (@lem3373593 _87647 _35313 _35315) (@lem3373575 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373598 (q : Prop) (p : Prop) (r : Prop) : (term280 p q r) = (term280 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3373599 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term284 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314).
Proof. exact (@lem3373598 (@IN _87647 _35315 _35316) (term277 _87647 _35313 _35315) (term286 _87647 _35316 _35313 _35314)). Qed.
Lemma lem3373629 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term265 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314).
Proof. exact (TRANS (@lem3373594 _87647 _35315 _35316 _35313 _35314) (@lem3373599 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3373631 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term287 _87647 _35315 _35316 _35313 _35314) = (term288 _87647 _35315 _35316 _35313 _35314).
Proof. exact (MK_COMB (@lem3373630) (@lem3373629 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373661 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term285 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314).
Proof. exact (eq_refl (term285 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373662 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : ((term265 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314)) = ((term285 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314)).
Proof. exact (MK_COMB (@lem3373631 _87647 _35315 _35316 _35313 _35314) (@lem3373661 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373664 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3373665 (x : Prop) : (x = x) = True.
Proof. exact (@lem3373664 Prop x). Qed.
Lemma lem3373666 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : ((term285 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314)) = True.
Proof. exact (@lem3373665 (term285 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373667 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : ((term265 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314)) = True.
Proof. exact (TRANS (@lem3373662 _87647 _35315 _35316 _35313 _35314) (@lem3373666 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373668 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : True = ((term265 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314)).
Proof. exact (SYM (@lem3373667 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373669 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term265 _87647 _35315 _35316 _35313 _35314) = (term285 _87647 _35315 _35316 _35313 _35314).
Proof. exact (EQ_MP (@lem3373668 _87647 _35315 _35316 _35313 _35314) (@lem0)). Qed.
Lemma lem3373670 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : term285 _87647 _35315 _35316 _35313 _35314.
Proof. exact (EQ_MP (@lem3373669 _87647 _35315 _35316 _35313 _35314) (@lem3373451 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373672 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3373673 {_87647 : Type'} (_35313 : _87647) (_35314 : _87647 -> Prop) (_35315 : _87647) (_35316 : _87647 -> Prop) : (term285 _87647 _35315 _35316 _35313 _35314) = (term289 _87647 _35313 _35314 _35315 _35316).
Proof. exact (@lem3373672 (term290 _87647 _35315 _35316 _35313 _35314) (@IN _87647 _35315 _35316)). Qed.
Lemma lem3373675 (a : Prop) (b : Prop) : (term291 a b) = (term292 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3373676 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term293 _87647 _35315 _35316 _35313 _35314) = (term294 _87647 _35315 _35316 _35313 _35314).
Proof. exact (@lem3373675 (term277 _87647 _35313 _35315) (term286 _87647 _35316 _35313 _35314)). Qed.
Lemma lem3373678 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3373679 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) : (term295 _87647 _35313 _35315) = (_35313 = _35315).
Proof. exact (@lem3373678 (_35313 = _35315)). Qed.
Lemma lem3373680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3373681 {_87647 : Type'} (_35313 : _87647) (_35315 : _87647) : (term296 _87647 _35313 _35315) = (term297 _87647 _35313 _35315).
Proof. exact (MK_COMB (@lem3373680) (@lem3373679 _87647 _35313 _35315)). Qed.
Lemma lem3373683 (a : Prop) (b : Prop) : (term291 a b) = (term292 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3373684 {_87647 : Type'} (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term298 _87647 _35316 _35313 _35314) = (term299 _87647 _35316 _35313 _35314).
Proof. exact (@lem3373683 (term282 _87647 _35314 _35316) (term249 _87647 _35313 _35314)). Qed.
Lemma lem3373686 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3373687 {_87647 : Type'} (_35314 : _87647 -> Prop) (_35316 : _87647 -> Prop) : (term300 _87647 _35314 _35316) = (_35314 = _35316).
Proof. exact (@lem3373686 (_35314 = _35316)). Qed.
Lemma lem3373688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3373689 {_87647 : Type'} (_35314 : _87647 -> Prop) (_35316 : _87647 -> Prop) : (term301 _87647 _35314 _35316) = (term302 _87647 _35314 _35316).
Proof. exact (MK_COMB (@lem3373688) (@lem3373687 _87647 _35314 _35316)). Qed.
Lemma lem3373691 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3373692 {_87647 : Type'} (_35313 : _87647) (_35314 : _87647 -> Prop) : (term303 _87647 _35313 _35314) = (@IN _87647 _35313 _35314).
Proof. exact (@lem3373691 (@IN _87647 _35313 _35314)). Qed.
Lemma lem3373693 {_87647 : Type'} (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term299 _87647 _35316 _35313 _35314) = (term304 _87647 _35316 _35313 _35314).
Proof. exact (MK_COMB (@lem3373689 _87647 _35314 _35316) (@lem3373692 _87647 _35313 _35314)). Qed.
Lemma lem3373694 {_87647 : Type'} (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term298 _87647 _35316 _35313 _35314) = (term304 _87647 _35316 _35313 _35314).
Proof. exact (TRANS (@lem3373684 _87647 _35316 _35313 _35314) (@lem3373693 _87647 _35316 _35313 _35314)). Qed.
Lemma lem3373695 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term294 _87647 _35315 _35316 _35313 _35314) = (term305 _87647 _35315 _35316 _35313 _35314).
Proof. exact (MK_COMB (@lem3373681 _87647 _35313 _35315) (@lem3373694 _87647 _35316 _35313 _35314)). Qed.
Lemma lem3373696 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term293 _87647 _35315 _35316 _35313 _35314) = (term305 _87647 _35315 _35316 _35313 _35314).
Proof. exact (TRANS (@lem3373676 _87647 _35315 _35316 _35313 _35314) (@lem3373695 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3373698 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) (_35313 : _87647) (_35314 : _87647 -> Prop) : (term306 _87647 _35315 _35316 _35313 _35314) = (term307 _87647 _35315 _35316 _35313 _35314).
Proof. exact (MK_COMB (@lem3373697) (@lem3373696 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373699 {_87647 : Type'} (_35315 : _87647) (_35316 : _87647 -> Prop) : (@IN _87647 _35315 _35316) = (@IN _87647 _35315 _35316).
Proof. exact (eq_refl (@IN _87647 _35315 _35316)). Qed.
Lemma lem3373700 {_87647 : Type'} (_35313 : _87647) (_35314 : _87647 -> Prop) (_35315 : _87647) (_35316 : _87647 -> Prop) : (term289 _87647 _35313 _35314 _35315 _35316) = (term308 _87647 _35313 _35314 _35315 _35316).
Proof. exact (MK_COMB (@lem3373698 _87647 _35315 _35316 _35313 _35314) (@lem3373699 _87647 _35315 _35316)). Qed.
Lemma lem3373701 {_87647 : Type'} (_35313 : _87647) (_35314 : _87647 -> Prop) (_35315 : _87647) (_35316 : _87647 -> Prop) : (term285 _87647 _35315 _35316 _35313 _35314) = (term308 _87647 _35313 _35314 _35315 _35316).
Proof. exact (TRANS (@lem3373673 _87647 _35313 _35314 _35315 _35316) (@lem3373700 _87647 _35313 _35314 _35315 _35316)). Qed.
Lemma lem3373703 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term309 _87647 x' s.
Proof. exact (conj (@lem3373549 _87647 s) (@lem3373556 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373704 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : term310 _87647 x'' x' s.
Proof. exact (conj (@lem3373540 _87647 _87658 x' s x f x'' t h1 h2) (@lem3373703 _87647 _87658 x' s x f x'' t h2)). Qed.
Lemma lem3373706 {_87647 : Type'} (_35313 : _87647) (_35314 : _87647 -> Prop) (_35315 : _87647) (_35316 : _87647 -> Prop) : term308 _87647 _35313 _35314 _35315 _35316.
Proof. exact (EQ_MP (@lem3373701 _87647 _35313 _35314 _35315 _35316) (@lem3373670 _87647 _35315 _35316 _35313 _35314)). Qed.
Lemma lem3373707 {_87647 : Type'} (_35313 : _87647) (_35314 : _87647 -> Prop) (_35315 : _87647) (_35316 : _87647 -> Prop) : term308 _87647 _35313 _35314 _35315 _35316.
Proof. exact (@lem3373706 _87647 _35313 _35314 _35315 _35316). Qed.
Lemma lem3373708 {_87647 : Type'} (x' : _87647) (x'' : _87647) (s : _87647 -> Prop) : term311 _87647 x' x'' s.
Proof. exact (@lem3373707 _87647 x' s x'' s). Qed.
Lemma lem3373711 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : @IN _87647 x'' s.
Proof. exact (@lem3373708 _87647 x' x'' s (@lem3373704 _87647 _87658 x' s x f x'' t h1 h2)). Qed.
Lemma lem3373712 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : term248 _87647 x'' s.
Proof. exact (fun h0 : term249 _87647 x'' s => @lem3373711 _87647 _87658 x' s x f x'' t h1 h2). Qed.
Lemma lem3373714 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373715 {_87647 : Type'} (x'' : _87647) (s : _87647 -> Prop) : (term248 _87647 x'' s) = (@IN _87647 x'' s).
Proof. exact (@lem3373714 (@IN _87647 x'' s)). Qed.
Lemma lem3373716 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : @IN _87647 x'' s.
Proof. exact (EQ_MP (@lem3373715 _87647 x'' s) (@lem3373712 _87647 _87658 x' s x f x'' t h1 h2)). Qed.
Lemma lem3373718 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : @IN _87647 x'' t.
Proof. exact (proj2 (@lem3372847 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373719 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term248 _87647 x'' t.
Proof. exact (fun h0 : term249 _87647 x'' t => @lem3373718 _87647 _87658 x' s x f x'' t h1). Qed.
Lemma lem3373721 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373722 {_87647 : Type'} (x'' : _87647) (t : _87647 -> Prop) : (term248 _87647 x'' t) = (@IN _87647 x'' t).
Proof. exact (@lem3373721 (@IN _87647 x'' t)). Qed.
Lemma lem3373723 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : @IN _87647 x'' t.
Proof. exact (EQ_MP (@lem3373722 _87647 x'' t) (@lem3373719 _87647 _87658 x' s x f x'' t h1)). Qed.
Lemma lem3373725 (a : Prop) (b : Prop) : (term250 a b) = (term251 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3373726 {_87647 : Type'} (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term77 _87647 s _35268 t) = (term76 _87647 s _35268 t).
Proof. exact (@lem3373725 (@IN _87647 _35268 s) (@IN _87647 _35268 t)). Qed.
Lemma lem3373727 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (_35268 : _87647) : (term312 _87647 _87658 x' f _35268) = (term312 _87647 _87658 x' f _35268).
Proof. exact (eq_refl (term312 _87647 _87658 x' f _35268)). Qed.
Lemma lem3373728 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term237 _87647 _87658 x' f s _35268 t) = (term313 _87647 _87658 x' f s _35268 t).
Proof. exact (MK_COMB (@lem3373727 _87647 _87658 x' f _35268) (@lem3373726 _87647 s _35268 t)). Qed.
Lemma lem3373730 (a : Prop) (b : Prop) : (term250 a b) = (term251 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3373731 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term313 _87647 _87658 x' f s _35268 t) = (term314 _87647 _87658 x' f s _35268 t).
Proof. exact (@lem3373730 ((f x') = (f _35268)) (term6 _87647 s _35268 t)). Qed.
Lemma lem3373732 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term237 _87647 _87658 x' f s _35268 t) = (term314 _87647 _87658 x' f s _35268 t).
Proof. exact (TRANS (@lem3373728 _87647 _87658 x' f s _35268 t) (@lem3373731 _87647 _87658 x' f s _35268 t)). Qed.
Lemma lem3373734 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3373735 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term314 _87647 _87658 x' f s _35268 t) = (term315 _87647 _87658 x' f s _35268 t).
Proof. exact (@lem3373734 (term316 _87647 _87658 x' f s _35268 t)). Qed.
Lemma lem3373736 {_87647 _87658 : Type'} (x' : _87647) (f : _87647 -> _87658) (s : _87647 -> Prop) (_35268 : _87647) (t : _87647 -> Prop) : (term237 _87647 _87658 x' f s _35268 t) = (term315 _87647 _87658 x' f s _35268 t).
Proof. exact (TRANS (@lem3373732 _87647 _87658 x' f s _35268 t) (@lem3373735 _87647 _87658 x' f s _35268 t)). Qed.
Lemma lem3373738 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : term6 _87647 s x'' t.
Proof. exact (conj (@lem3373716 _87647 _87658 x' s x f x'' t h1 h2) (@lem3373723 _87647 _87658 x' s x f x'' t h2)). Qed.
Lemma lem3373739 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : term316 _87647 _87658 x' f s x'' t.
Proof. exact (conj (@lem3373472 _87647 _87658 x' s x f x'' t h2) (@lem3373738 _87647 _87658 x' s x f x'' t h1 h2)). Qed.
Lemma lem3373741 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term315 _87647 _87658 x' f s _35268 t.
Proof. exact (EQ_MP (@lem3373736 _87647 _87658 x' f s _35268 t) (@lem3373251 _87647 _87658 _35268 x' s x f x'' t h1)). Qed.
Lemma lem3373742 {_87647 _87658 : Type'} (_35268 : _87647) (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term315 _87647 _87658 x' f s _35268 t.
Proof. exact (@lem3373741 _87647 _87658 _35268 x' s x f x'' t h1). Qed.
Lemma lem3373743 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term181 _87647 _87658 x' s x f x'' t) : term315 _87647 _87658 x' f s x'' t.
Proof. exact (@lem3373742 _87647 _87658 x'' x' s x f x'' t h1). Qed.
Lemma lem3373746 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : False.
Proof. exact (@lem3373743 _87647 _87658 x' s x f x'' t h2 (@lem3373739 _87647 _87658 x' s x f x'' t h1 h2)). Qed.
Lemma lem3373747 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : term257.
Proof. exact (fun h0 : ~ False => @lem3373746 _87647 _87658 x' s x f x'' t h1 h2). Qed.
Lemma lem3373749 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3373750 : term257 = False.
Proof. exact (@lem3373749 False). Qed.
Lemma lem3373752 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term181 _87647 _87658 x' s x f x'' t) : False.
Proof. exact (EQ_MP (@lem3373750) (@lem3373747 _87647 _87658 x' s x f x'' t h1 h2)). Qed.
Lemma lem3373753 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (EQ_MP (@lem3373431) (@lem3373428 _87647 _87658 x' s x f t h1 h2)). Qed.
Lemma lem3373754 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (EQ_MP (@lem3373361) (@lem3373358 _87647 _87658 x' s x f t h1 h2)). Qed.
Lemma lem3373755 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : (term99 _87647 _87658 x f t) = False.
Proof. exact (prop_ext (fun h3 : term99 _87647 _87658 x f t => @lem3373753 _87647 _87658 x' s x f t h1 h2) (fun h3 : False => @lem3372934 _87647 _87658 x f t h1)). Qed.
Lemma lem3373756 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f t) (h2 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (EQ_MP (@lem3373755 _87647 _87658 x' s x f t h1 h2) (@lem3372934 _87647 _87658 x f t h1)). Qed.
Lemma lem3373757 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : (term99 _87647 _87658 x f s) = False.
Proof. exact (prop_ext (fun h3 : term99 _87647 _87658 x f s => @lem3373754 _87647 _87658 x' s x f t h1 h2) (fun h3 : False => @lem3372893 _87647 _87658 x f s h1)). Qed.
Lemma lem3373758 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term99 _87647 _87658 x f s) (h2 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (EQ_MP (@lem3373757 _87647 _87658 x' s x f t h1 h2) (@lem3372893 _87647 _87658 x f s h1)). Qed.
Lemma lem3373759 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term128 _87647 _87658 x' s x f t) : False.
Proof. exact (or_elim (@lem3372837 _87647 _87658 x' s x f t h1) (fun h0 : term99 _87647 _87658 x f s => @lem3373758 _87647 _87658 x' s x f t h0 h1) (fun h0 : term99 _87647 _87658 x f t => @lem3373756 _87647 _87658 x' s x f t h0 h1)). Qed.
Lemma lem3373760 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term218 _87647 _87658 x' s x f x'' t) : False.
Proof. exact (or_elim (@lem3372834 _87647 _87658 x' s x f x'' t h2) (fun h0 : term128 _87647 _87658 x' s x f t => @lem3373759 _87647 _87658 x' s x f t h0) (fun h0 : term181 _87647 _87658 x' s x f x'' t => @lem3373752 _87647 _87658 x' s x f x'' t h1 h0)). Qed.
Lemma lem3373761 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term218 _87647 _87658 x' s x f x'' t) : (term218 _87647 _87658 x' s x f x'' t) = False.
Proof. exact (prop_ext (fun h3 : term218 _87647 _87658 x' s x f x'' t => @lem3373760 _87647 _87658 x' s x f x'' t h1 h2) (fun h3 : False => @lem3372834 _87647 _87658 x' s x f x'' t h2)). Qed.
Lemma lem3373762 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (x'' : _87647) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term218 _87647 _87658 x' s x f x'' t) : False.
Proof. exact (EQ_MP (@lem3373761 _87647 _87658 x' s x f x'' t h1 h2) (@lem3372834 _87647 _87658 x' s x f x'' t h2)). Qed.
Lemma lem3373763 {_87647 _87658 : Type'} (x' : _87647) (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term221 _87647 _87658 x' s x f t) : False.
Proof. exact (ex_elim (@lem3372662 _87647 _87658 x' s x f t h2) (fun x'' : _87647 => fun h0 : term220 _87647 _87658 x' s x f t x'' => @lem3373762 _87647 _87658 x' s x f x'' t h1 h0)). Qed.
Lemma lem3373764 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term70 _87647 _87658 s x f t) : False.
Proof. exact (ex_elim (@lem3372661 _87647 _87658 s x f t h2) (fun x' : _87647 => fun h0 : term222 _87647 _87658 s x f t x' => @lem3373763 _87647 _87658 x' s x f t h1 h0)). Qed.
Lemma lem3373765 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term70 _87647 _87658 s x f t) : (term70 _87647 _87658 s x f t) = False.
Proof. exact (prop_ext (fun h3 : term70 _87647 _87658 s x f t => @lem3373764 _87647 _87658 s x f t h1 h2) (fun h3 : False => @lem3372021 _87647 _87658 s x f t h2)). Qed.
Lemma lem3373766 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (f : _87647 -> _87658) (t : _87647 -> Prop) (h1 : term68 _87647 _87658 f) (h2 : term70 _87647 _87658 s x f t) : False.
Proof. exact (EQ_MP (@lem3373765 _87647 _87658 s x f t h1 h2) (@lem3372021 _87647 _87658 s x f t h2)). Qed.
Lemma lem3373767 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (t : _87647 -> Prop) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term69 _87647 _87658 s x f t.
Proof. exact (fun h0 : term70 _87647 _87658 s x f t => @lem3373766 _87647 _87658 s x f t h1 h0). Qed.
Lemma lem3373768 {_87647 _87658 : Type'} (s : _87647 -> Prop) (x : _87658) (t : _87647 -> Prop) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : (term28 _87647 _87658 x f s t) = (term35 _87647 _87658 s x f t).
Proof. exact (EQ_MP (@lem3372020 _87647 _87658 s x f t) (@lem3373767 _87647 _87658 s x t f h1)). Qed.
Lemma lem3373773 {_87647 _87658 : Type'} (s : _87647 -> Prop) (t : _87647 -> Prop) (f : _87647 -> _87658) (h1 : term68 _87647 _87658 f) : term38 _87647 _87658 s f t.
Proof. exact (fun x : _87658 => @lem3373768 _87647 _87658 s x t f h1). Qed.
Lemma lem3373774 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) (t : _87647 -> Prop) : term41 _87647 _87658 s f t.
Proof. exact (fun h0 : term68 _87647 _87658 f => @lem3373773 _87647 _87658 s t f h0). Qed.
Lemma lem3373779 {_87647 _87658 : Type'} (s : _87647 -> Prop) (f : _87647 -> _87658) : term45 _87647 _87658 s f.
Proof. exact (fun t : _87647 -> Prop => @lem3373774 _87647 _87658 s f t). Qed.
Lemma lem3373784 {_87647 _87658 : Type'} (f : _87647 -> _87658) : term49 _87647 _87658 f.
Proof. exact (fun s : _87647 -> Prop => @lem3373779 _87647 _87658 s f). Qed.
Lemma lem3373789 {_87647 _87658 : Type'} : term53 _87647 _87658.
Proof. exact (fun f : _87647 -> _87658 => @lem3373784 _87647 _87658 f). Qed.
Lemma lem3373790 {_87647 _87658 : Type'} : term55 _87647 _87658.
Proof. exact (EQ_MP (@lem3372015 _87647 _87658) (@lem3373789 _87647 _87658)). Qed.
Lemma lem3373792 {_87647 _87658 : Type'} : term55 _87647 _87658.
Proof. exact (@lem3371690 _87647 _87658 (@lem3373790 _87647 _87658)). Qed.
Lemma lem3373793 {_87647 _87658 : Type'} (h1 : term56 _87647 _87658) : False.
Proof. exact (@lem3373792 _87647 _87658 (@lem3371674 _87647 _87658 h1)). Qed.
Lemma lem3373794 {_87647 _87658 : Type'} (h1 : term56 _87647 _87658) : (term56 _87647 _87658) = False.
Proof. exact (prop_ext (fun h2 : term56 _87647 _87658 => @lem3373793 _87647 _87658 h1) (fun h2 : False => @lem3371674 _87647 _87658 h1)). Qed.
Lemma lem3373795 {_87647 _87658 : Type'} (h1 : term56 _87647 _87658) : False.
Proof. exact (EQ_MP (@lem3373794 _87647 _87658 h1) (@lem3371674 _87647 _87658 h1)). Qed.
Lemma lem3373796 {_87647 _87658 : Type'} : term55 _87647 _87658.
Proof. exact (fun h0 : term56 _87647 _87658 => @lem3373795 _87647 _87658 h0). Qed.
Lemma lem3373797 {_87647 _87658 : Type'} : term53 _87647 _87658.
Proof. exact (EQ_MP (@lem3371673 _87647 _87658) (@lem3373796 _87647 _87658)). Qed.
Lemma lem3373798 {_87647 _87658 : Type'} : term52 _87647 _87658.
Proof. exact (EQ_MP (@lem3371669 _87647 _87658) (@lem3373797 _87647 _87658)). Qed.
