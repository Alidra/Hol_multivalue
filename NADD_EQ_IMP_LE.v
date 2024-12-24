Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_EQ_IMP_LE_term_abbrevs.
Require Import nadd_eq_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1247096_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1279654 (m : nat) : term0 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1279655 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1279656 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1279655 m) (@lem1279654 m)). Qed.
Lemma lem1279657 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1279656 m n). Qed.
Lemma lem1279658 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1279659 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem1279658 n m) (@lem1279657 m n)). Qed.
Lemma lem1279660 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem1279659 n m p). Qed.
Lemma lem1279661 (n : nat) (m : nat) (p : nat) : (term4 n m p) = ((term5 m n p) = (term6 n m p)).
Proof. exact (eq_refl (term4 n m p)). Qed.
Lemma lem1279663 (x : nadd) : term7 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1279664 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1279665 (x : nadd) : term8 x.
Proof. exact (EQ_MP (@lem1279664 x) (@lem1279663 x)). Qed.
Lemma lem1279666 (x : nadd) (y : nadd) : term9 x y.
Proof. exact (@lem1279665 x y). Qed.
Lemma lem1279667 (x : nadd) (y : nadd) : (term9 x y) = ((nadd_le x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1279669 (x : nadd) : term11 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1279670 (x : nadd) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1279671 (x : nadd) : term12 x.
Proof. exact (EQ_MP (@lem1279670 x) (@lem1279669 x)). Qed.
Lemma lem1279672 (x : nadd) (y : nadd) : term13 x y.
Proof. exact (@lem1279671 x y). Qed.
Lemma lem1279673 (x : nadd) (y : nadd) : (term13 x y) = ((nadd_eq x y) = (term14 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1279678 (x : nadd) (y : nadd) : (nadd_eq x y) = (term14 x y).
Proof. exact (EQ_MP (@lem1279673 x y) (@lem1279672 x y)). Qed.
Lemma lem1279688 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1279661 n m p) (@lem1279660 n m p)). Qed.
Lemma lem1279689 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term15 x y n B) = (term16 y x n B).
Proof. exact (@lem1279688 (dest_nadd y n) (dest_nadd x n) B). Qed.
Lemma lem1279692 (y : nadd) (x : nadd) (B : nat) : (term17 x y B) = (term18 y x B).
Proof. exact (fun_ext (fun n : nat => @lem1279689 y x n B)). Qed.
Lemma lem1279693 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279694 (y : nadd) (x : nadd) (B : nat) : (term19 x y B) = (term20 y x B).
Proof. exact (MK_COMB (@lem1279693) (@lem1279692 y x B)). Qed.
Lemma lem1279699 (y : nadd) (x : nadd) : (term21 x y) = (term22 y x).
Proof. exact (fun_ext (fun B : nat => @lem1279694 y x B)). Qed.
Lemma lem1279700 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1279701 (y : nadd) (x : nadd) : (term14 x y) = (term23 y x).
Proof. exact (MK_COMB (@lem1279700) (@lem1279699 y x)). Qed.
Lemma lem1279706 (y : nadd) (x : nadd) : (nadd_eq x y) = (term23 y x).
Proof. exact (TRANS (@lem1279678 x y) (@lem1279701 y x)). Qed.
Lemma lem1279707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1279708 (y : nadd) (x : nadd) : (term24 x y) = (term25 y x).
Proof. exact (MK_COMB (@lem1279707) (@lem1279706 y x)). Qed.
Lemma lem1279710 (x : nadd) (y : nadd) : (nadd_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1279667 x y) (@lem1279666 x y)). Qed.
Lemma lem1279719 (x : nadd) (y : nadd) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1279708 y x) (@lem1279710 x y)). Qed.
Lemma lem1279722 (x : nadd) (y : nadd) : (term27 x y) = (term26 x y).
Proof. exact (SYM (@lem1279719 x y)). Qed.
Lemma lem1279723 (y : nadd) (x : nadd) (h1 : term23 y x) : term23 y x.
Proof. exact (h1). Qed.
Lemma lem1279724 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : term20 y x B.
Proof. exact (h1). Qed.
Lemma lem1279725 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : term28 y x B n.
Proof. exact (@lem1279724 y x B h1 n). Qed.
Lemma lem1279726 (y : nadd) (x : nadd) (n : nat) (B : nat) : (term28 y x B n) = (term16 y x n B).
Proof. exact (eq_refl (term28 y x B n)). Qed.
Lemma lem1279727 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : term16 y x n B.
Proof. exact (EQ_MP (@lem1279726 y x n B) (@lem1279725 n y x B h1)). Qed.
Lemma lem1279731 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : term29 x y n B.
Proof. exact (proj1 (@lem1279727 n y x B h1)). Qed.
Lemma lem1279732 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term29 x y n B) = ((term29 x y n B) = True).
Proof. exact (@lem7 (term29 x y n B)). Qed.
Lemma lem1279739 (n : nat) (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : (term29 x y n B) = True.
Proof. exact (EQ_MP (@lem1279732 x y n B) (@lem1279731 n y x B h1)). Qed.
Lemma lem1279740 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : (term30 x y B) = term31.
Proof. exact (fun_ext (fun n : nat => @lem1279739 n y x B h1)). Qed.
Lemma lem1279741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279742 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : (term32 x y B) = term33.
Proof. exact (MK_COMB (@lem1279741) (@lem1279740 y x B h1)). Qed.
Lemma lem1279744 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1279745 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1279744 nat t). Qed.
Lemma lem1279746 : term33 = True.
Proof. exact (@lem1279745 True). Qed.
Lemma lem1279747 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : (term32 x y B) = True.
Proof. exact (TRANS (@lem1279742 y x B h1) (@lem1279746)). Qed.
Lemma lem1279748 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : True = (term32 x y B).
Proof. exact (SYM (@lem1279747 y x B h1)). Qed.
Lemma lem1279749 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : term32 x y B.
Proof. exact (EQ_MP (@lem1279748 y x B h1) (@lem0)). Qed.
Lemma lem1279750 (y : nadd) (x : nadd) (B : nat) (h1 : term20 y x B) : term10 x y.
Proof. exact (ex_intro (term36 x y) B (@lem1279749 y x B h1)). Qed.
Lemma lem1279751 (y : nadd) (x : nadd) (h1 : term23 y x) : term10 x y.
Proof. exact (ex_elim (@lem1279723 y x h1) (fun B : nat => fun h0 : term22 y x B => @lem1279750 y x B h0)). Qed.
Lemma lem1279752 (x : nadd) (y : nadd) : term27 x y.
Proof. exact (fun h0 : term23 y x => @lem1279751 y x h0). Qed.
Lemma lem1279753 (x : nadd) (y : nadd) : term26 x y.
Proof. exact (EQ_MP (@lem1279722 x y) (@lem1279752 x y)). Qed.
Lemma lem1279758 (x : nadd) : term37 x.
Proof. exact (fun y : nadd => @lem1279753 x y). Qed.
Lemma lem1279763 : term38.
Proof. exact (fun x : nadd => @lem1279758 x). Qed.
