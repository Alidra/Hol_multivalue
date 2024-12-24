Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380526_term_abbrevs.
Require Import thm4372172_spec.
Require Import thm4372173_spec.
Require Import thm4372190_spec.
Require Import thm4372254_spec.
Require Import thm4372255_spec.
Require Import thm4372272_spec.
Require Import thm4372722_spec.
Require Import thm4373017_spec.
Require Import thm4373351_spec.
Require Import thm4374535_spec.
Require Import thm4374857_spec.
Require Import thm4377169_spec.
Lemma lem4380505 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : term0 _104908 g) : (term1 _104907 _104908 f g) = (term2 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4373351 _104907 _104908 f g) (@lem4377169 _104907 _104908 f g h1 h2)). Qed.
Lemma lem4380506 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : term0 _104908 g) : (term0 _104908 g) = ((term1 _104907 _104908 f g) = (term2 _104907 _104908 f g)).
Proof. exact (prop_ext (fun h3 : term0 _104908 g => @lem4380505 _104907 _104908 f g h1 h2) (fun h3 : (term1 _104907 _104908 f g) = (term2 _104907 _104908 f g) => @lem4372272 _104908 g h2)). Qed.
Lemma lem4380507 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : term0 _104908 g) : (term1 _104907 _104908 f g) = (term2 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4380506 _104907 _104908 f g h1 h2) (@lem4372272 _104908 g h2)). Qed.
Lemma lem4380508 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term0 _104907 f) : term3 _104907 _104908 f g.
Proof. exact (fun h0 : term0 _104908 g => @lem4380507 _104907 _104908 f g h1 h0). Qed.
Lemma lem4380509 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : g = (@EMPTY (_104908 -> Prop))) : (term1 _104907 _104908 f g) = (term4 _104907 _104908 f).
Proof. exact (EQ_MP (@lem4373017 _104907 _104908 f g h2) (@lem4374857 _104907 _104908 f g h1 h2)). Qed.
Lemma lem4380510 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : g = (@EMPTY (_104908 -> Prop))) : (g = (@EMPTY (_104908 -> Prop))) = ((term1 _104907 _104908 f g) = (term4 _104907 _104908 f)).
Proof. exact (prop_ext (fun h3 : g = (@EMPTY (_104908 -> Prop)) => @lem4380509 _104907 _104908 f g h1 h2) (fun h3 : (term1 _104907 _104908 f g) = (term4 _104907 _104908 f) => @lem4372255 _104908 g h2)). Qed.
Lemma lem4380511 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term0 _104907 f) (h2 : g = (@EMPTY (_104908 -> Prop))) : (term1 _104907 _104908 f g) = (term4 _104907 _104908 f).
Proof. exact (EQ_MP (@lem4380510 _104907 _104908 f g h1 h2) (@lem4372255 _104908 g h2)). Qed.
Lemma lem4380512 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term0 _104907 f) : term5 _104907 _104908 g f.
Proof. exact (fun h0 : g = (@EMPTY (_104908 -> Prop)) => @lem4380511 _104907 _104908 f g h1 h0). Qed.
Lemma lem4380513 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term0 _104907 f) : term6 _104907 _104908 f g.
Proof. exact (conj (@lem4380512 _104907 _104908 g f h1) (@lem4380508 _104907 _104908 g f h1)). Qed.
Lemma lem4380517 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term0 _104907 f) : (term1 _104907 _104908 f g) = (term7 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4372254 _104907 _104908 f g) (@lem4380513 _104907 _104908 g f h1)). Qed.
Lemma lem4380518 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term0 _104907 f) : (term0 _104907 f) = ((term1 _104907 _104908 f g) = (term7 _104907 _104908 f g)).
Proof. exact (prop_ext (fun h2 : term0 _104907 f => @lem4380517 _104907 _104908 g f h1) (fun h2 : (term1 _104907 _104908 f g) = (term7 _104907 _104908 f g) => @lem4372190 _104907 f h1)). Qed.
Lemma lem4380519 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term0 _104907 f) : (term1 _104907 _104908 f g) = (term7 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4380518 _104907 _104908 g f h1) (@lem4372190 _104907 f h1)). Qed.
Lemma lem4380520 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term8 _104907 _104908 f g.
Proof. exact (fun h0 : term0 _104907 f => @lem4380519 _104907 _104908 g f h0). Qed.
Lemma lem4380521 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term1 _104907 _104908 f g) = (term9 _104907 _104908 g).
Proof. exact (EQ_MP (@lem4372722 _104907 _104908 g f h1) (@lem4374535 _104907 _104908 g f h1)). Qed.
Lemma lem4380522 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (f = (@EMPTY (_104907 -> Prop))) = ((term1 _104907 _104908 f g) = (term9 _104907 _104908 g)).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY (_104907 -> Prop)) => @lem4380521 _104907 _104908 g f h1) (fun h2 : (term1 _104907 _104908 f g) = (term9 _104907 _104908 g) => @lem4372173 _104907 f h1)). Qed.
Lemma lem4380523 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : (term1 _104907 _104908 f g) = (term9 _104907 _104908 g).
Proof. exact (EQ_MP (@lem4380522 _104907 _104908 g f h1) (@lem4372173 _104907 f h1)). Qed.
Lemma lem4380524 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term10 _104907 _104908 f g.
Proof. exact (fun h0 : f = (@EMPTY (_104907 -> Prop)) => @lem4380523 _104907 _104908 g f h0). Qed.
Lemma lem4380525 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term11 _104907 _104908 f g.
Proof. exact (conj (@lem4380524 _104907 _104908 f g) (@lem4380520 _104907 _104908 f g)). Qed.
Lemma lem4380526 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term1 _104907 _104908 f g) = (term12 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4372172 _104907 _104908 f g) (@lem4380525 _104907 _104908 f g)). Qed.
