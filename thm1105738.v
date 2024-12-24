Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105738_term_abbrevs.
Require Import thm1105308_spec.
Require Import thm1105686_spec.
Lemma lem1105687 {_25569 : Type'} : (term0 _25569) = (term1 _25569).
Proof. exact (eq_refl (term0 _25569)). Qed.
Lemma lem1105688 {_25569 : Type'} : term1 _25569.
Proof. exact (EQ_MP (@lem1105687 _25569) (@lem1105308 _25569)). Qed.
Lemma lem1105689 {_25569 : Type'} : term2 _25569.
Proof. exact (@lem1105688 _25569 term3). Qed.
Lemma lem1105690 {_25569 : Type'} : (term2 _25569) = (term4 _25569).
Proof. exact (eq_refl (term2 _25569)). Qed.
Lemma lem1105691 {_25569 : Type'} : term4 _25569.
Proof. exact (EQ_MP (@lem1105690 _25569) (@lem1105689 _25569)). Qed.
Lemma lem1105692 {_25569 : Type'} (h1 : (@EL _25569) = (term5 _25569)) : (@EL _25569) = (term5 _25569).
Proof. exact (h1). Qed.
Lemma lem1105693 {_25569 : Type'} (h1 : (@EL _25569) = (term5 _25569)) : (term5 _25569) = (@EL _25569).
Proof. exact (SYM (@lem1105692 _25569 h1)). Qed.
Lemma lem1105694 {_25569 : Type'} (h1 : (term5 _25569) = (@EL _25569)) : (term5 _25569) = (@EL _25569).
Proof. exact (h1). Qed.
Lemma lem1105695 {_25569 : Type'} (h1 : (term5 _25569) = (@EL _25569)) : (@EL _25569) = (term5 _25569).
Proof. exact (SYM (@lem1105694 _25569 h1)). Qed.
Lemma lem1105696 {_25569 : Type'} : ((@EL _25569) = (term5 _25569)) = ((term5 _25569) = (@EL _25569)).
Proof. exact (prop_ext (fun h1 : (@EL _25569) = (term5 _25569) => @lem1105693 _25569 h1) (fun h1 : (term5 _25569) = (@EL _25569) => @lem1105695 _25569 h1)). Qed.
Lemma lem1105699 {_25569 : Type'} : (term5 _25569) = (@EL _25569).
Proof. exact (EQ_MP (@lem1105696 _25569) (@lem1105686 _25569)). Qed.
Lemma lem1105700 {_25569 : Type'} : (term5 _25569) = (@EL _25569).
Proof. exact (@lem1105699 _25569). Qed.
Lemma lem1105701 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1105702 {_25569 : Type'} : (term6 _25569) = (term7 _25569).
Proof. exact (MK_COMB (@lem1105700 _25569) (@lem1105701)). Qed.
Lemma lem1105703 {_25569 : Type'} (l : list _25569) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1105704 {_25569 : Type'} (l : list _25569) : (term8 _25569 l) = (term9 _25569 l).
Proof. exact (MK_COMB (@lem1105702 _25569) (@lem1105703 _25569 l)). Qed.
Lemma lem1105705 {_25569 : Type'} : (@eq _25569) = (@eq _25569).
Proof. exact (eq_refl (@eq _25569)). Qed.
Lemma lem1105706 {_25569 : Type'} (l : list _25569) : (term10 _25569 l) = (term11 _25569 l).
Proof. exact (MK_COMB (@lem1105705 _25569) (@lem1105704 _25569 l)). Qed.
Lemma lem1105707 {_25569 : Type'} (l : list _25569) : (@hd _25569 l) = (@hd _25569 l).
Proof. exact (eq_refl (@hd _25569 l)). Qed.
Lemma lem1105708 {_25569 : Type'} (l : list _25569) : ((term8 _25569 l) = (@hd _25569 l)) = ((term9 _25569 l) = (@hd _25569 l)).
Proof. exact (MK_COMB (@lem1105706 _25569 l) (@lem1105707 _25569 l)). Qed.
Lemma lem1105709 {_25569 : Type'} : (term12 _25569) = (term13 _25569).
Proof. exact (fun_ext (fun l : list _25569 => @lem1105708 _25569 l)). Qed.
Lemma lem1105710 {_25569 : Type'} : (@all (list _25569)) = (@all (list _25569)).
Proof. exact (eq_refl (@all (list _25569))). Qed.
Lemma lem1105711 {_25569 : Type'} : (term14 _25569) = (term15 _25569).
Proof. exact (MK_COMB (@lem1105710 _25569) (@lem1105709 _25569)). Qed.
Lemma lem1105712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1105713 {_25569 : Type'} : (term16 _25569) = (term17 _25569).
Proof. exact (MK_COMB (@lem1105712) (@lem1105711 _25569)). Qed.
Lemma lem1105715 {_25569 : Type'} : (term5 _25569) = (@EL _25569).
Proof. exact (EQ_MP (@lem1105696 _25569) (@lem1105686 _25569)). Qed.
Lemma lem1105716 {_25569 : Type'} : (term5 _25569) = (@EL _25569).
Proof. exact (@lem1105715 _25569). Qed.
Lemma lem1105717 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1105718 {_25569 : Type'} (n : nat) : (term18 _25569 n) = (term19 _25569 n).
Proof. exact (MK_COMB (@lem1105716 _25569) (@lem1105717 n)). Qed.
Lemma lem1105719 {_25569 : Type'} (l : list _25569) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1105720 {_25569 : Type'} (n : nat) (l : list _25569) : (term20 _25569 n l) = (term21 _25569 n l).
Proof. exact (MK_COMB (@lem1105718 _25569 n) (@lem1105719 _25569 l)). Qed.
Lemma lem1105721 {_25569 : Type'} : (@eq _25569) = (@eq _25569).
Proof. exact (eq_refl (@eq _25569)). Qed.
Lemma lem1105722 {_25569 : Type'} (n : nat) (l : list _25569) : (term22 _25569 n l) = (term23 _25569 n l).
Proof. exact (MK_COMB (@lem1105721 _25569) (@lem1105720 _25569 n l)). Qed.
Lemma lem1105724 {_25569 : Type'} : (term5 _25569) = (@EL _25569).
Proof. exact (EQ_MP (@lem1105696 _25569) (@lem1105686 _25569)). Qed.
Lemma lem1105725 {_25569 : Type'} : (term5 _25569) = (@EL _25569).
Proof. exact (@lem1105724 _25569). Qed.
Lemma lem1105726 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1105727 {_25569 : Type'} (n : nat) : (term24 _25569 n) = (@EL _25569 n).
Proof. exact (MK_COMB (@lem1105725 _25569) (@lem1105726 n)). Qed.
Lemma lem1105728 {_25569 : Type'} (l : list _25569) : (@tl _25569 l) = (@tl _25569 l).
Proof. exact (eq_refl (@tl _25569 l)). Qed.
Lemma lem1105729 {_25569 : Type'} (n : nat) (l : list _25569) : (term25 _25569 n l) = (term26 _25569 n l).
Proof. exact (MK_COMB (@lem1105727 _25569 n) (@lem1105728 _25569 l)). Qed.
Lemma lem1105730 {_25569 : Type'} (n : nat) (l : list _25569) : ((term20 _25569 n l) = (term25 _25569 n l)) = ((term21 _25569 n l) = (term26 _25569 n l)).
Proof. exact (MK_COMB (@lem1105722 _25569 n l) (@lem1105729 _25569 n l)). Qed.
Lemma lem1105731 {_25569 : Type'} (n : nat) : (term27 _25569 n) = (term28 _25569 n).
Proof. exact (fun_ext (fun l : list _25569 => @lem1105730 _25569 n l)). Qed.
Lemma lem1105732 {_25569 : Type'} : (@all (list _25569)) = (@all (list _25569)).
Proof. exact (eq_refl (@all (list _25569))). Qed.
Lemma lem1105733 {_25569 : Type'} (n : nat) : (term29 _25569 n) = (term30 _25569 n).
Proof. exact (MK_COMB (@lem1105732 _25569) (@lem1105731 _25569 n)). Qed.
Lemma lem1105734 {_25569 : Type'} : (term31 _25569) = (term32 _25569).
Proof. exact (fun_ext (fun n : nat => @lem1105733 _25569 n)). Qed.
Lemma lem1105735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1105736 {_25569 : Type'} : (term33 _25569) = (term34 _25569).
Proof. exact (MK_COMB (@lem1105735) (@lem1105734 _25569)). Qed.
Lemma lem1105737 {_25569 : Type'} : (term4 _25569) = (term35 _25569).
Proof. exact (MK_COMB (@lem1105713 _25569) (@lem1105736 _25569)). Qed.
Lemma lem1105738 {_25569 : Type'} : term35 _25569.
Proof. exact (EQ_MP (@lem1105737 _25569) (@lem1105691 _25569)). Qed.
