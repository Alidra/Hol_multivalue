Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CASES_term_abbrevs.
Require Import ITERATE_CASES_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7028554 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7028556 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7028557 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7028556 A B h1 op). Qed.
Lemma lem7028558 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7028559 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7028558 A B op) (@lem7028557 A B op h1)). Qed.
Lemma lem7028560 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7028561 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7028559 A B op h1 (@lem7028560 B op h2)). Qed.
Lemma lem7028562 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7028561 A B op h0 h1). Qed.
Lemma lem7028563 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7028564 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7028562 A B op h2 (@lem7028563 A B h1)). Qed.
Lemma lem7028565 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7028564 A B op h1 h0). Qed.
Lemma lem7028566 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7028565 A B op h1). Qed.
Lemma lem7028567 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7028566 A B h0). Qed.
Lemma lem7028568 {A B : Type'} : term0 A B.
Proof. exact (@lem7028567 A B (@lem6160738 A B)). Qed.
Lemma lem7028569 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7028568 A B op). Qed.
Lemma lem7028570 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7028599 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7028600 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7028599 A). Qed.
Lemma lem7028601 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7028602 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7028600 A) (@lem7028601 A s)). Qed.
Lemma lem7028603 {A : Type'} (P : A -> Prop) (f : A -> nat) (g : A -> nat) : (term6 A P f g) = (term6 A P f g).
Proof. exact (eq_refl (term6 A P f g)). Qed.
Lemma lem7028604 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) (g : A -> nat) : (term7 A s P f g) = (term8 A s P f g).
Proof. exact (MK_COMB (@lem7028602 A s) (@lem7028603 A P f g)). Qed.
Lemma lem7028605 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7028606 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) (g : A -> nat) : (term9 A s P f g) = (term10 A s P f g).
Proof. exact (MK_COMB (@lem7028605) (@lem7028604 A s P f g)). Qed.
Lemma lem7028608 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7028609 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7028608 A). Qed.
Lemma lem7028616 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term11 A s P) = (term11 A s P).
Proof. exact (eq_refl (term11 A s P)). Qed.
Lemma lem7028617 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term12 A s P) = (term13 A s P).
Proof. exact (MK_COMB (@lem7028609 A) (@lem7028616 A s P)). Qed.
Lemma lem7028618 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7028619 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term14 A s P f) = (term15 A s P f).
Proof. exact (MK_COMB (@lem7028617 A s P) (@lem7028618 A f)). Qed.
Lemma lem7028620 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7028621 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term16 A s P f) = (term17 A s P f).
Proof. exact (MK_COMB (@lem7028620) (@lem7028619 A s P f)). Qed.
Lemma lem7028623 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7028624 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7028623 A). Qed.
Lemma lem7028631 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term18 A s P) = (term18 A s P).
Proof. exact (eq_refl (term18 A s P)). Qed.
Lemma lem7028632 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term19 A s P) = (term20 A s P).
Proof. exact (MK_COMB (@lem7028624 A) (@lem7028631 A s P)). Qed.
Lemma lem7028633 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7028634 {A : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> nat) : (term21 A s P g) = (term22 A s P g).
Proof. exact (MK_COMB (@lem7028632 A s P) (@lem7028633 A g)). Qed.
Lemma lem7028635 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : A -> Prop) (g : A -> nat) : (term23 A f s P g) = (term24 A f s P g).
Proof. exact (MK_COMB (@lem7028621 A s P f) (@lem7028634 A s P g)). Qed.
Lemma lem7028636 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : A -> Prop) (g : A -> nat) : ((term7 A s P f g) = (term23 A f s P g)) = ((term8 A s P f g) = (term24 A f s P g)).
Proof. exact (MK_COMB (@lem7028606 A s P f g) (@lem7028635 A f s P g)). Qed.
Lemma lem7028639 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem7028640 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : A -> Prop) (g : A -> nat) : (term26 A f s P g) = (term27 A f s P g).
Proof. exact (MK_COMB (@lem7028639 A s) (@lem7028636 A f s P g)). Qed.
Lemma lem7028643 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : A -> Prop) : (term28 A f s P) = (term29 A f s P).
Proof. exact (fun_ext (fun g : A -> nat => @lem7028640 A f s P g)). Qed.
Lemma lem7028644 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7028645 {A : Type'} (f : A -> nat) (s : A -> Prop) (P : A -> Prop) : (term30 A f s P) = (term31 A f s P).
Proof. exact (MK_COMB (@lem7028644 A) (@lem7028643 A f s P)). Qed.
Lemma lem7028650 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term32 A s P) = (term33 A s P).
Proof. exact (fun_ext (fun f : A -> nat => @lem7028645 A f s P)). Qed.
Lemma lem7028651 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7028652 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term34 A s P) = (term35 A s P).
Proof. exact (MK_COMB (@lem7028651 A) (@lem7028650 A s P)). Qed.
Lemma lem7028657 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem7028652 A s P)). Qed.
Lemma lem7028658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7028659 {A : Type'} (s : A -> Prop) : (term38 A s) = (term39 A s).
Proof. exact (MK_COMB (@lem7028658 A) (@lem7028657 A s)). Qed.
Lemma lem7028664 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7028659 A s)). Qed.
Lemma lem7028665 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7028666 {A : Type'} : (term42 A) = (term43 A).
Proof. exact (MK_COMB (@lem7028665 A) (@lem7028664 A)). Qed.
Lemma lem7028671 {A : Type'} : (term43 A) = (term42 A).
Proof. exact (SYM (@lem7028666 A)). Qed.
Lemma lem7028673 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7028570 A B op) (@lem7028569 A B op)). Qed.
Lemma lem7028674 {A : Type'} (op : type1606) : term44 A op.
Proof. exact (@lem7028673 A nat op). Qed.
Lemma lem7028675 {A : Type'} : term45 A.
Proof. exact (@lem7028674 A Nat.add). Qed.
Lemma lem7028677 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7028554) (@lem6924403)). Qed.
Lemma lem7028678 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7028677)). Qed.
Lemma lem7028679 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7028678) (@lem0)). Qed.
Lemma lem7028680 {A : Type'} : term43 A.
Proof. exact (@lem7028675 A (@lem7028679)). Qed.
Lemma lem7028681 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem7028671 A) (@lem7028680 A)). Qed.
