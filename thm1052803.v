Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1052803_term_abbrevs.
Require Import thm1052523_spec.
Require Import thm1052775_spec.
Lemma lem1052776 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem1052777 : term1.
Proof. exact (EQ_MP (@lem1052776) (@lem1052523)). Qed.
Lemma lem1052778 : term2.
Proof. exact (@lem1052777 term3). Qed.
Lemma lem1052779 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem1052780 : term4.
Proof. exact (EQ_MP (@lem1052779) (@lem1052778)). Qed.
Lemma lem1052781 (h1 : NUMSND = term5) : NUMSND = term5.
Proof. exact (h1). Qed.
Lemma lem1052782 (h1 : NUMSND = term5) : term5 = NUMSND.
Proof. exact (SYM (@lem1052781 h1)). Qed.
Lemma lem1052783 (h1 : term5 = NUMSND) : term5 = NUMSND.
Proof. exact (h1). Qed.
Lemma lem1052784 (h1 : term5 = NUMSND) : NUMSND = term5.
Proof. exact (SYM (@lem1052783 h1)). Qed.
Lemma lem1052785 : (NUMSND = term5) = (term5 = NUMSND).
Proof. exact (prop_ext (fun h1 : NUMSND = term5 => @lem1052782 h1) (fun h1 : term5 = NUMSND => @lem1052784 h1)). Qed.
Lemma lem1052788 : term5 = NUMSND.
Proof. exact (EQ_MP (@lem1052785) (@lem1052775)). Qed.
Lemma lem1052789 (x : nat) (y : nat) : (NUMPAIR x y) = (NUMPAIR x y).
Proof. exact (eq_refl (NUMPAIR x y)). Qed.
Lemma lem1052790 (x : nat) (y : nat) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1052788) (@lem1052789 x y)). Qed.
Lemma lem1052791 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1052792 (x : nat) (y : nat) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1052791) (@lem1052790 x y)). Qed.
Lemma lem1052793 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1052794 (x : nat) (y : nat) : ((term6 x y) = y) = ((term7 x y) = y).
Proof. exact (MK_COMB (@lem1052792 x y) (@lem1052793 y)). Qed.
Lemma lem1052795 (y : nat) (x : nat) : (term10 y x) = (term10 y x).
Proof. exact (eq_refl (term10 y x)). Qed.
Lemma lem1052796 (x : nat) (y : nat) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1052795 y x) (@lem1052794 x y)). Qed.
Lemma lem1052797 (x : nat) : (term13 x) = (term14 x).
Proof. exact (fun_ext (fun y : nat => @lem1052796 x y)). Qed.
Lemma lem1052798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1052799 (x : nat) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1052798) (@lem1052797 x)). Qed.
Lemma lem1052800 : term17 = term18.
Proof. exact (fun_ext (fun x : nat => @lem1052799 x)). Qed.
Lemma lem1052801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1052802 : term4 = term19.
Proof. exact (MK_COMB (@lem1052801) (@lem1052800)). Qed.
Lemma lem1052803 : term19.
Proof. exact (EQ_MP (@lem1052802) (@lem1052780)). Qed.
