Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7919719_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Lemma lem7919643 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem7919644 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem7919645 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem7919644 A B y) (@lem7919643 A B y)). Qed.
Lemma lem7919646 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem7919645 A B y s). Qed.
Lemma lem7919647 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem7919648 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem7919647 A B y s) (@lem7919646 A B y s)). Qed.
Lemma lem7919649 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem7919648 A B y s f). Qed.
Lemma lem7919650 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem7919652 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7919653 {A : Type'} (x : A) : (term7 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem7919654 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7919653 A x) (@lem7919652 A x)). Qed.
Lemma lem7919655 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7919657 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7919658 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem7919659 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem7919658 A s) (@lem7919657 A s)). Qed.
Lemma lem7919660 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (@lem7919659 A s t). Qed.
Lemma lem7919661 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = ((s = t) = (term11 A s t)).
Proof. exact (eq_refl (term10 A s t)). Qed.
Lemma lem7919666 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem7919661 A s t) (@lem7919660 A s t)). Qed.
Lemma lem7919667 {A B : Type'} (s : type36 A B) (t : type36 A B) : (s = t) = (term12 A B s t).
Proof. exact (@lem7919666 (finite_prod A B) s t). Qed.
Lemma lem7919668 {A B : Type'} : ((@UNIV (finite_prod A B)) = (term13 A B)) = (term14 A B).
Proof. exact (@lem7919667 A B (@UNIV (finite_prod A B)) (term13 A B)). Qed.
Lemma lem7919678 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7919655 A x) (@lem7919654 A x)). Qed.
Lemma lem7919679 {A B : Type'} (x : finite_prod A B) : (@IN (finite_prod A B) x (@UNIV (finite_prod A B))) = True.
Proof. exact (@lem7919678 (finite_prod A B) x). Qed.
Lemma lem7919680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7919681 {A B : Type'} (x : finite_prod A B) : (term15 A B x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7919680) (@lem7919679 A B x)). Qed.
Lemma lem7919683 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem7919650 A B y f s) (@lem7919649 A B y s f)). Qed.
Lemma lem7919684 {A B : Type'} (y : finite_prod A B) (f : type1558 A B) (s : nat -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (@lem7919683 nat (finite_prod A B) y f s). Qed.
Lemma lem7919685 {A B : Type'} (x : finite_prod A B) : (term18 A B x) = (term19 A B x).
Proof. exact (@lem7919684 A B x (@mk_finite_prod A B) (term20 A B)). Qed.
Lemma lem7919696 {A B : Type'} (x : finite_prod A B) : ((@IN (finite_prod A B) x (@UNIV (finite_prod A B))) = (term18 A B x)) = (True = (term19 A B x)).
Proof. exact (MK_COMB (@lem7919681 A B x) (@lem7919685 A B x)). Qed.
Lemma lem7919698 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7919699 {A B : Type'} (x : finite_prod A B) : (True = (term19 A B x)) = (term19 A B x).
Proof. exact (@lem7919698 (term19 A B x)). Qed.
Lemma lem7919710 {A B : Type'} (x : finite_prod A B) : ((@IN (finite_prod A B) x (@UNIV (finite_prod A B))) = (term18 A B x)) = (term19 A B x).
Proof. exact (TRANS (@lem7919696 A B x) (@lem7919699 A B x)). Qed.
Lemma lem7919711 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (fun_ext (fun x : finite_prod A B => @lem7919710 A B x)). Qed.
Lemma lem7919712 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7919713 {A B : Type'} : (term14 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem7919712 A B) (@lem7919711 A B)). Qed.
Lemma lem7919718 {A B : Type'} : ((@UNIV (finite_prod A B)) = (term13 A B)) = (term23 A B).
Proof. exact (TRANS (@lem7919668 A B) (@lem7919713 A B)). Qed.
Lemma lem7919719 {A B : Type'} : (term23 A B) = ((@UNIV (finite_prod A B)) = (term13 A B)).
Proof. exact (SYM (@lem7919718 A B)). Qed.
