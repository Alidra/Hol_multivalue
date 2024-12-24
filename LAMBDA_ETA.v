Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_ETA_term_abbrevs.
Require Import CART_EQ_spec.
Require Import LAMBDA_BETA_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem7624601 {A B : Type'} (g : nat -> A) (i : nat) : term0 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7624602 {A B : Type'} (g : nat -> A) (i : nat) : (term0 A B g i) = (term1 A B g i).
Proof. exact (eq_refl (term0 A B g i)). Qed.
Lemma lem7624603 {A B : Type'} (g : nat -> A) (i : nat) : term1 A B g i.
Proof. exact (EQ_MP (@lem7624602 A B g i) (@lem7624601 A B g i)). Qed.
Lemma lem7624604 {A B : Type'} (g : nat -> A) (i : nat) : (term1 A B g i) = ((term1 A B g i) = True).
Proof. exact (@lem7 (term1 A B g i)). Qed.
Lemma lem7624606 {A B : Type'} (x : cart A B) : term2 A B x.
Proof. exact (@lem7617066 A B x). Qed.
Lemma lem7624607 {A B : Type'} (x : cart A B) : (term2 A B x) = (term3 A B x).
Proof. exact (eq_refl (term2 A B x)). Qed.
Lemma lem7624608 {A B : Type'} (x : cart A B) : term3 A B x.
Proof. exact (EQ_MP (@lem7624607 A B x) (@lem7624606 A B x)). Qed.
Lemma lem7624609 {A B : Type'} (x : cart A B) (y : cart A B) : term4 A B x y.
Proof. exact (@lem7624608 A B x y). Qed.
Lemma lem7624610 {A B : Type'} (x : cart A B) (y : cart A B) : (term4 A B x y) = ((x = y) = (term5 A B x y)).
Proof. exact (eq_refl (term4 A B x y)). Qed.
Lemma lem7624619 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term5 A B x y).
Proof. exact (EQ_MP (@lem7624610 A B x y) (@lem7624609 A B x y)). Qed.
Lemma lem7624620 {_139958 _139962 : Type'} (x : cart _139958 _139962) (y : cart _139958 _139962) : (x = y) = (term5 _139958 _139962 x y).
Proof. exact (@lem7624619 _139958 _139962 x y). Qed.
Lemma lem7624621 {_139958 _139962 : Type'} (g : cart _139958 _139962) : ((term6 _139958 _139962 g) = g) = (term7 _139958 _139962 g).
Proof. exact (@lem7624620 _139958 _139962 (term6 _139958 _139962 g) g). Qed.
Lemma lem7624627 {A B : Type'} (g : nat -> A) (i : nat) : (term1 A B g i) = True.
Proof. exact (EQ_MP (@lem7624604 A B g i) (@lem7624603 A B g i)). Qed.
Lemma lem7624628 {_139958 _139962 : Type'} (g : nat -> _139958) (i : nat) : (term1 _139958 _139962 g i) = True.
Proof. exact (@lem7624627 _139958 _139962 g i). Qed.
Lemma lem7624629 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : (term8 _139958 _139962 g i) = True.
Proof. exact (@lem7624628 _139958 _139962 (term9 _139958 _139962 g) i). Qed.
Lemma lem7624630 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : (term10 _139958 _139962 g i) = (@dollar _139958 _139962 g i).
Proof. exact (eq_refl (term10 _139958 _139962 g i)). Qed.
Lemma lem7624631 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : (term11 _139958 _139962 g i) = (term11 _139958 _139962 g i).
Proof. exact (eq_refl (term11 _139958 _139962 g i)). Qed.
Lemma lem7624632 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : ((term12 _139958 _139962 g i) = (term10 _139958 _139962 g i)) = ((term12 _139958 _139962 g i) = (@dollar _139958 _139962 g i)).
Proof. exact (MK_COMB (@lem7624631 _139958 _139962 g i) (@lem7624630 _139958 _139962 g i)). Qed.
Lemma lem7624633 {_139962 : Type'} (i : nat) : (term13 _139962 i) = (term13 _139962 i).
Proof. exact (eq_refl (term13 _139962 i)). Qed.
Lemma lem7624634 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : (term8 _139958 _139962 g i) = (term14 _139958 _139962 g i).
Proof. exact (MK_COMB (@lem7624633 _139962 i) (@lem7624632 _139958 _139962 g i)). Qed.
Lemma lem7624635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7624636 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : (term15 _139958 _139962 g i) = (term16 _139958 _139962 g i).
Proof. exact (MK_COMB (@lem7624635) (@lem7624634 _139958 _139962 g i)). Qed.
Lemma lem7624637 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7624638 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : ((term8 _139958 _139962 g i) = True) = ((term14 _139958 _139962 g i) = True).
Proof. exact (MK_COMB (@lem7624636 _139958 _139962 g i) (@lem7624637)). Qed.
Lemma lem7624639 {_139958 _139962 : Type'} (g : cart _139958 _139962) (i : nat) : (term14 _139958 _139962 g i) = True.
Proof. exact (EQ_MP (@lem7624638 _139958 _139962 g i) (@lem7624629 _139958 _139962 g i)). Qed.
Lemma lem7624640 {_139958 _139962 : Type'} (g : cart _139958 _139962) : (term17 _139958 _139962 g) = term18.
Proof. exact (fun_ext (fun i : nat => @lem7624639 _139958 _139962 g i)). Qed.
Lemma lem7624641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7624642 {_139958 _139962 : Type'} (g : cart _139958 _139962) : (term7 _139958 _139962 g) = term19.
Proof. exact (MK_COMB (@lem7624641) (@lem7624640 _139958 _139962 g)). Qed.
Lemma lem7624644 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7624645 (t : Prop) : (term21 t) = t.
Proof. exact (@lem7624644 nat t). Qed.
Lemma lem7624646 : term19 = True.
Proof. exact (@lem7624645 True). Qed.
Lemma lem7624647 {_139958 _139962 : Type'} (g : cart _139958 _139962) : (term7 _139958 _139962 g) = True.
Proof. exact (TRANS (@lem7624642 _139958 _139962 g) (@lem7624646)). Qed.
Lemma lem7624648 {_139958 _139962 : Type'} (g : cart _139958 _139962) : ((term6 _139958 _139962 g) = g) = True.
Proof. exact (TRANS (@lem7624621 _139958 _139962 g) (@lem7624647 _139958 _139962 g)). Qed.
Lemma lem7624649 {_139958 _139962 : Type'} : (term22 _139958 _139962) = (term23 _139958 _139962).
Proof. exact (fun_ext (fun g : cart _139958 _139962 => @lem7624648 _139958 _139962 g)). Qed.
Lemma lem7624650 {_139958 _139962 : Type'} : (@all (cart _139958 _139962)) = (@all (cart _139958 _139962)).
Proof. exact (eq_refl (@all (cart _139958 _139962))). Qed.
Lemma lem7624651 {_139958 _139962 : Type'} : (term24 _139958 _139962) = (term25 _139958 _139962).
Proof. exact (MK_COMB (@lem7624650 _139958 _139962) (@lem7624649 _139958 _139962)). Qed.
Lemma lem7624653 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7624654 {_139958 _139962 : Type'} (t : Prop) : (term26 _139958 _139962 t) = t.
Proof. exact (@lem7624653 (cart _139958 _139962) t). Qed.
Lemma lem7624655 {_139958 _139962 : Type'} : (term25 _139958 _139962) = True.
Proof. exact (@lem7624654 _139958 _139962 True). Qed.
Lemma lem7624656 {_139958 _139962 : Type'} : (term24 _139958 _139962) = True.
Proof. exact (TRANS (@lem7624651 _139958 _139962) (@lem7624655 _139958 _139962)). Qed.
Lemma lem7624657 {_139958 _139962 : Type'} : True = (term24 _139958 _139962).
Proof. exact (SYM (@lem7624656 _139958 _139962)). Qed.
Lemma lem7624658 {_139958 _139962 : Type'} : term24 _139958 _139962.
Proof. exact (EQ_MP (@lem7624657 _139958 _139962) (@lem0)). Qed.
