Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_IMAGE_term_abbrevs.
Require Import ITERATE_IMAGE_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6961568 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6961570 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem6961571 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem6961570 A B C h1 op). Qed.
Lemma lem6961572 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem6961573 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem6961572 A B C op) (@lem6961571 A B C op h1)). Qed.
Lemma lem6961574 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem6961575 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem6961573 A B C op h1 (@lem6961574 C op h2)). Qed.
Lemma lem6961576 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem6961575 A B C op h0 h1). Qed.
Lemma lem6961577 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem6961578 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem6961576 A B C op h2 (@lem6961577 A B C h1)). Qed.
Lemma lem6961579 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem6961578 A B C op h1 h0). Qed.
Lemma lem6961580 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem6961579 A B C op h1). Qed.
Lemma lem6961581 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem6961580 A B C h0). Qed.
Lemma lem6961582 {A B C : Type'} : term0 A B C.
Proof. exact (@lem6961581 A B C (@lem5942955 A B C)). Qed.
Lemma lem6961583 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem6961582 A B C op). Qed.
Lemma lem6961584 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem6961627 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6961628 {_127560 : Type'} : (@nsum _127560) = (@iterate nat _127560 Nat.add).
Proof. exact (@lem6961627 _127560). Qed.
Lemma lem6961629 {_127560 _127584 : Type'} (f : _127584 -> _127560) (s : _127584 -> Prop) : (@IMAGE _127584 _127560 f s) = (@IMAGE _127584 _127560 f s).
Proof. exact (eq_refl (@IMAGE _127584 _127560 f s)). Qed.
Lemma lem6961630 {_127560 _127584 : Type'} (f : _127584 -> _127560) (s : _127584 -> Prop) : (term6 _127560 _127584 f s) = (term7 _127560 _127584 f s).
Proof. exact (MK_COMB (@lem6961628 _127560) (@lem6961629 _127560 _127584 f s)). Qed.
Lemma lem6961631 {_127560 : Type'} (g : _127560 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6961632 {_127560 _127584 : Type'} (f : _127584 -> _127560) (s : _127584 -> Prop) (g : _127560 -> nat) : (term8 _127560 _127584 f s g) = (term9 _127560 _127584 f s g).
Proof. exact (MK_COMB (@lem6961630 _127560 _127584 f s) (@lem6961631 _127560 g)). Qed.
Lemma lem6961633 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6961634 {_127560 _127584 : Type'} (f : _127584 -> _127560) (s : _127584 -> Prop) (g : _127560 -> nat) : (term10 _127560 _127584 f s g) = (term11 _127560 _127584 f s g).
Proof. exact (MK_COMB (@lem6961633) (@lem6961632 _127560 _127584 f s g)). Qed.
Lemma lem6961636 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6961637 {_127584 : Type'} : (@nsum _127584) = (@iterate nat _127584 Nat.add).
Proof. exact (@lem6961636 _127584). Qed.
Lemma lem6961638 {_127584 : Type'} (s : _127584 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6961639 {_127584 : Type'} (s : _127584 -> Prop) : (@nsum _127584 s) = (@iterate nat _127584 Nat.add s).
Proof. exact (MK_COMB (@lem6961637 _127584) (@lem6961638 _127584 s)). Qed.
Lemma lem6961640 {_127560 _127584 : Type'} (g : _127560 -> nat) (f : _127584 -> _127560) : (@o _127584 _127560 nat g f) = (@o _127584 _127560 nat g f).
Proof. exact (eq_refl (@o _127584 _127560 nat g f)). Qed.
Lemma lem6961641 {_127560 _127584 : Type'} (s : _127584 -> Prop) (g : _127560 -> nat) (f : _127584 -> _127560) : (term12 _127560 _127584 s g f) = (term13 _127560 _127584 s g f).
Proof. exact (MK_COMB (@lem6961639 _127584 s) (@lem6961640 _127560 _127584 g f)). Qed.
Lemma lem6961642 {_127560 _127584 : Type'} (s : _127584 -> Prop) (g : _127560 -> nat) (f : _127584 -> _127560) : ((term8 _127560 _127584 f s g) = (term12 _127560 _127584 s g f)) = ((term9 _127560 _127584 f s g) = (term13 _127560 _127584 s g f)).
Proof. exact (MK_COMB (@lem6961634 _127560 _127584 f s g) (@lem6961641 _127560 _127584 s g f)). Qed.
Lemma lem6961645 {_127560 _127584 : Type'} (s : _127584 -> Prop) (f : _127584 -> _127560) : (term14 _127560 _127584 s f) = (term14 _127560 _127584 s f).
Proof. exact (eq_refl (term14 _127560 _127584 s f)). Qed.
Lemma lem6961646 {_127560 _127584 : Type'} (s : _127584 -> Prop) (g : _127560 -> nat) (f : _127584 -> _127560) : (term15 _127560 _127584 s g f) = (term16 _127560 _127584 s g f).
Proof. exact (MK_COMB (@lem6961645 _127560 _127584 s f) (@lem6961642 _127560 _127584 s g f)). Qed.
Lemma lem6961649 {_127560 _127584 : Type'} (g : _127560 -> nat) (f : _127584 -> _127560) : (term17 _127560 _127584 g f) = (term18 _127560 _127584 g f).
Proof. exact (fun_ext (fun s : _127584 -> Prop => @lem6961646 _127560 _127584 s g f)). Qed.
Lemma lem6961650 {_127584 : Type'} : (@all (_127584 -> Prop)) = (@all (_127584 -> Prop)).
Proof. exact (eq_refl (@all (_127584 -> Prop))). Qed.
Lemma lem6961651 {_127560 _127584 : Type'} (g : _127560 -> nat) (f : _127584 -> _127560) : (term19 _127560 _127584 g f) = (term20 _127560 _127584 g f).
Proof. exact (MK_COMB (@lem6961650 _127584) (@lem6961649 _127560 _127584 g f)). Qed.
Lemma lem6961656 {_127560 _127584 : Type'} (f : _127584 -> _127560) : (term21 _127560 _127584 f) = (term22 _127560 _127584 f).
Proof. exact (fun_ext (fun g : _127560 -> nat => @lem6961651 _127560 _127584 g f)). Qed.
Lemma lem6961657 {_127560 : Type'} : (@all (_127560 -> nat)) = (@all (_127560 -> nat)).
Proof. exact (eq_refl (@all (_127560 -> nat))). Qed.
Lemma lem6961658 {_127560 _127584 : Type'} (f : _127584 -> _127560) : (term23 _127560 _127584 f) = (term24 _127560 _127584 f).
Proof. exact (MK_COMB (@lem6961657 _127560) (@lem6961656 _127560 _127584 f)). Qed.
Lemma lem6961663 {_127560 _127584 : Type'} : (term25 _127560 _127584) = (term26 _127560 _127584).
Proof. exact (fun_ext (fun f : _127584 -> _127560 => @lem6961658 _127560 _127584 f)). Qed.
Lemma lem6961664 {_127560 _127584 : Type'} : (@all (_127584 -> _127560)) = (@all (_127584 -> _127560)).
Proof. exact (eq_refl (@all (_127584 -> _127560))). Qed.
Lemma lem6961665 {_127560 _127584 : Type'} : (term27 _127560 _127584) = (term28 _127560 _127584).
Proof. exact (MK_COMB (@lem6961664 _127560 _127584) (@lem6961663 _127560 _127584)). Qed.
Lemma lem6961670 {_127560 _127584 : Type'} : (term28 _127560 _127584) = (term27 _127560 _127584).
Proof. exact (SYM (@lem6961665 _127560 _127584)). Qed.
Lemma lem6961672 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem6961584 A B C op) (@lem6961583 A B C op)). Qed.
Lemma lem6961673 {_127560 _127584 : Type'} (op : type1606) : term29 _127560 _127584 op.
Proof. exact (@lem6961672 _127584 _127560 nat op). Qed.
Lemma lem6961674 {_127560 _127584 : Type'} : term30 _127560 _127584.
Proof. exact (@lem6961673 _127560 _127584 Nat.add). Qed.
Lemma lem6961676 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6961568) (@lem6924403)). Qed.
Lemma lem6961677 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6961676)). Qed.
Lemma lem6961678 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6961677) (@lem0)). Qed.
Lemma lem6961679 {_127560 _127584 : Type'} : term28 _127560 _127584.
Proof. exact (@lem6961674 _127560 _127584 (@lem6961678)). Qed.
Lemma lem6961680 {_127560 _127584 : Type'} : term27 _127560 _127584.
Proof. exact (EQ_MP (@lem6961670 _127560 _127584) (@lem6961679 _127560 _127584)). Qed.
