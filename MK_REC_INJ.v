Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MK_REC_INJ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1059614 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term0 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1059615 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term0 A r) = r).
Proof. exact (@lem1059614 A r). Qed.
Lemma lem1059616 {A : Type'} (x : type1597 A) : (@ZRECSPACE A x) = ((term0 A x) = x).
Proof. exact (@lem1059615 A x). Qed.
Lemma lem1059619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1059620 {A : Type'} (x : type1597 A) : (term1 A x) = (term2 A x).
Proof. exact (MK_COMB (@lem1059619) (@lem1059616 A x)). Qed.
Lemma lem1059622 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term0 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1059623 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term0 A r) = r).
Proof. exact (@lem1059622 A r). Qed.
Lemma lem1059624 {A : Type'} (y : type1597 A) : (@ZRECSPACE A y) = ((term0 A y) = y).
Proof. exact (@lem1059623 A y). Qed.
Lemma lem1059627 {A : Type'} (x : type1597 A) (y : type1597 A) : (term3 A x y) = (term4 A x y).
Proof. exact (MK_COMB (@lem1059620 A x) (@lem1059624 A y)). Qed.
Lemma lem1059630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1059631 {A : Type'} (x : type1597 A) (y : type1597 A) : (term5 A x y) = (term6 A x y).
Proof. exact (MK_COMB (@lem1059630) (@lem1059627 A x y)). Qed.
Lemma lem1059634 {A : Type'} (x : type1597 A) (y : type1597 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1059635 {A : Type'} (x : type1597 A) (y : type1597 A) : (term7 A x y) = (term8 A x y).
Proof. exact (MK_COMB (@lem1059631 A x y) (@lem1059634 A x y)). Qed.
Lemma lem1059638 {A : Type'} (x : type1597 A) (y : type1597 A) : (term8 A x y) = (term7 A x y).
Proof. exact (SYM (@lem1059635 A x y)). Qed.
Lemma lem1059639 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : term4 A x y.
Proof. exact (h1). Qed.
Lemma lem1059641 {A : Type'} (x : type1597 A) (h1 : (term0 A x) = x) : (term0 A x) = x.
Proof. exact (h1). Qed.
Lemma lem1059642 {A : Type'} (x : type1597 A) (h1 : (term0 A x) = x) : x = (term0 A x).
Proof. exact (SYM (@lem1059641 A x h1)). Qed.
Lemma lem1059643 {A : Type'} (x : type1597 A) (h1 : x = (term0 A x)) : x = (term0 A x).
Proof. exact (h1). Qed.
Lemma lem1059644 {A : Type'} (x : type1597 A) (h1 : x = (term0 A x)) : (term0 A x) = x.
Proof. exact (SYM (@lem1059643 A x h1)). Qed.
Lemma lem1059645 {A : Type'} (x : type1597 A) : ((term0 A x) = x) = (x = (term0 A x)).
Proof. exact (prop_ext (fun h1 : (term0 A x) = x => @lem1059642 A x h1) (fun h1 : x = (term0 A x) => @lem1059644 A x h1)). Qed.
Lemma lem1059646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1059647 {A : Type'} (x : type1597 A) : (term2 A x) = (term9 A x).
Proof. exact (MK_COMB (@lem1059646) (@lem1059645 A x)). Qed.
Lemma lem1059648 {A : Type'} (y : type1597 A) (h1 : (term0 A y) = y) : (term0 A y) = y.
Proof. exact (h1). Qed.
Lemma lem1059649 {A : Type'} (y : type1597 A) (h1 : (term0 A y) = y) : y = (term0 A y).
Proof. exact (SYM (@lem1059648 A y h1)). Qed.
Lemma lem1059650 {A : Type'} (y : type1597 A) (h1 : y = (term0 A y)) : y = (term0 A y).
Proof. exact (h1). Qed.
Lemma lem1059651 {A : Type'} (y : type1597 A) (h1 : y = (term0 A y)) : (term0 A y) = y.
Proof. exact (SYM (@lem1059650 A y h1)). Qed.
Lemma lem1059652 {A : Type'} (y : type1597 A) : ((term0 A y) = y) = (y = (term0 A y)).
Proof. exact (prop_ext (fun h1 : (term0 A y) = y => @lem1059649 A y h1) (fun h1 : y = (term0 A y) => @lem1059651 A y h1)). Qed.
Lemma lem1059653 {A : Type'} (x : type1597 A) (y : type1597 A) : (term4 A x y) = (term10 A x y).
Proof. exact (MK_COMB (@lem1059647 A x) (@lem1059652 A y)). Qed.
Lemma lem1059654 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : term10 A x y.
Proof. exact (EQ_MP (@lem1059653 A x y) (@lem1059639 A x y h1)). Qed.
Lemma lem1059660 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : x = (term0 A x).
Proof. exact (proj1 (@lem1059654 A x y h1)). Qed.
Lemma lem1059661 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1059662 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : (@eq (nat -> A -> Prop) x) = (term11 A x).
Proof. exact (MK_COMB (@lem1059661 A) (@lem1059660 A x y h1)). Qed.
Lemma lem1059664 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : y = (term0 A y).
Proof. exact (proj2 (@lem1059654 A x y h1)). Qed.
Lemma lem1059665 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : (x = y) = ((term0 A x) = (term0 A y)).
Proof. exact (MK_COMB (@lem1059662 A x y h1) (@lem1059664 A x y h1)). Qed.
Lemma lem1059666 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) : ((term0 A x) = (term0 A y)) = (x = y).
Proof. exact (SYM (@lem1059665 A x y h1)). Qed.
Lemma lem1059670 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : (@_mk_rec A x) = (@_mk_rec A y).
Proof. exact (h1). Qed.
Lemma lem1059671 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1059672 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : (term0 A x) = (term0 A y).
Proof. exact (MK_COMB (@lem1059671 A) (@lem1059670 A x y h1)). Qed.
Lemma lem1059673 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1059674 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : (term11 A x) = (term11 A y).
Proof. exact (MK_COMB (@lem1059673 A) (@lem1059672 A x y h1)). Qed.
Lemma lem1059675 {A : Type'} (y : type1597 A) : (term0 A y) = (term0 A y).
Proof. exact (eq_refl (term0 A y)). Qed.
Lemma lem1059676 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : ((term0 A x) = (term0 A y)) = ((term0 A y) = (term0 A y)).
Proof. exact (MK_COMB (@lem1059674 A x y h1) (@lem1059675 A y)). Qed.
Lemma lem1059678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1059679 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1059678 (type1597 A) x). Qed.
Lemma lem1059680 {A : Type'} (y : type1597 A) : ((term0 A y) = (term0 A y)) = True.
Proof. exact (@lem1059679 A (term0 A y)). Qed.
Lemma lem1059681 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : ((term0 A x) = (term0 A y)) = True.
Proof. exact (TRANS (@lem1059676 A x y h1) (@lem1059680 A y)). Qed.
Lemma lem1059682 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : True = ((term0 A x) = (term0 A y)).
Proof. exact (SYM (@lem1059681 A x y h1)). Qed.
Lemma lem1059683 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : (term0 A x) = (term0 A y).
Proof. exact (EQ_MP (@lem1059682 A x y h1) (@lem0)). Qed.
Lemma lem1059684 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : term4 A x y) (h2 : (@_mk_rec A x) = (@_mk_rec A y)) : x = y.
Proof. exact (EQ_MP (@lem1059666 A x y h1) (@lem1059683 A x y h2)). Qed.
Lemma lem1059685 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : term8 A x y.
Proof. exact (fun h0 : term4 A x y => @lem1059684 A x y h0 h1). Qed.
Lemma lem1059686 {A : Type'} (x : type1597 A) (y : type1597 A) (h1 : (@_mk_rec A x) = (@_mk_rec A y)) : term7 A x y.
Proof. exact (EQ_MP (@lem1059638 A x y) (@lem1059685 A x y h1)). Qed.
Lemma lem1059687 {A : Type'} (x : type1597 A) (y : type1597 A) : term12 A x y.
Proof. exact (fun h0 : (@_mk_rec A x) = (@_mk_rec A y) => @lem1059686 A x y h0). Qed.
Lemma lem1059692 {A : Type'} (x : type1597 A) : term13 A x.
Proof. exact (fun y : type1597 A => @lem1059687 A x y). Qed.
Lemma lem1059697 {A : Type'} : term14 A.
Proof. exact (fun x : type1597 A => @lem1059692 A x). Qed.
