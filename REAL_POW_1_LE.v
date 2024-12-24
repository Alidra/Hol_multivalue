Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_1_LE_term_abbrevs.
Require Import REAL_POW_LE2_spec.
Require Import REAL_POW_ONE_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1636790 (n : nat) : term0 n.
Proof. exact (@lem1636714 n). Qed.
Lemma lem1636791 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1636792 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1636791 n) (@lem1636790 n)). Qed.
Lemma lem1636793 (n : nat) (x : real) : term2 n x.
Proof. exact (@lem1636792 n x). Qed.
Lemma lem1636794 (x : real) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem1636795 (x : real) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem1636794 x n) (@lem1636793 n x)). Qed.
Lemma lem1636796 (x : real) (n : nat) : term4 x n.
Proof. exact (@lem1636795 x n term5). Qed.
Lemma lem1636797 (x : real) (n : nat) : (term4 x n) = (term6 x n).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem1636798 (x : real) (n : nat) : term6 x n.
Proof. exact (EQ_MP (@lem1636797 x n) (@lem1636796 x n)). Qed.
Lemma lem1636799 (x : real) (h1 : term7 x) : term7 x.
Proof. exact (h1). Qed.
Lemma lem1636800 (x : real) (h1 : term8 x) : term8 x.
Proof. exact (h1). Qed.
Lemma lem1636801 (x : real) (h1 : term9 x) : term9 x.
Proof. exact (h1). Qed.
Lemma lem1636802 (n : nat) : term10 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1636803 (n : nat) : (term10 n) = ((term11 n) = term5).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1636805 (x : real) : (term9 x) = ((term9 x) = True).
Proof. exact (@lem7 (term9 x)). Qed.
Lemma lem1636807 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1636816 (x : real) (h1 : term9 x) : (term9 x) = True.
Proof. exact (EQ_MP (@lem1636805 x) (@lem1636801 x h1)). Qed.
Lemma lem1636817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1636818 (x : real) (h1 : term9 x) : (term12 x) = (and True).
Proof. exact (MK_COMB (@lem1636817) (@lem1636816 x h1)). Qed.
Lemma lem1636820 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1636807 x) (@lem1636800 x h1)). Qed.
Lemma lem1636821 (x : real) (h1 : term8 x) (h2 : term9 x) : (term7 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1636818 x h2) (@lem1636820 x h1)). Qed.
Lemma lem1636823 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1636824 : (True /\ True) = True.
Proof. exact (@lem1636823 True). Qed.
Lemma lem1636825 (x : real) (h1 : term8 x) (h2 : term9 x) : (term7 x) = True.
Proof. exact (TRANS (@lem1636821 x h1 h2) (@lem1636824)). Qed.
Lemma lem1636826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1636827 (x : real) (h1 : term8 x) (h2 : term9 x) : (term13 x) = (imp True).
Proof. exact (MK_COMB (@lem1636826) (@lem1636825 x h1 h2)). Qed.
Lemma lem1636829 (n : nat) : (term11 n) = term5.
Proof. exact (EQ_MP (@lem1636803 n) (@lem1636802 n)). Qed.
Lemma lem1636830 (x : real) (n : nat) : (term14 x n) = (term14 x n).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem1636831 (x : real) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (MK_COMB (@lem1636830 x n) (@lem1636829 n)). Qed.
Lemma lem1636832 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term6 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1636827 x h1 h2) (@lem1636831 x n)). Qed.
Lemma lem1636834 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1636835 (x : real) (n : nat) : (term17 x n) = (term16 x n).
Proof. exact (@lem1636834 (term16 x n)). Qed.
Lemma lem1636836 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term6 x n) = (term16 x n).
Proof. exact (TRANS (@lem1636832 n x h1 h2) (@lem1636835 x n)). Qed.
Lemma lem1636837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1636838 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem1636837) (@lem1636836 n x h1 h2)). Qed.
Lemma lem1636839 (x : real) (n : nat) : (term16 x n) = (term16 x n).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem1636840 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term20 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem1636838 n x h1 h2) (@lem1636839 x n)). Qed.
Lemma lem1636842 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1636843 (x : real) (n : nat) : (term21 x n) = True.
Proof. exact (@lem1636842 (term16 x n)). Qed.
Lemma lem1636844 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term20 x n) = True.
Proof. exact (TRANS (@lem1636840 n x h1 h2) (@lem1636843 x n)). Qed.
Lemma lem1636845 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : True = (term20 x n).
Proof. exact (SYM (@lem1636844 n x h1 h2)). Qed.
Lemma lem1636846 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : term20 x n.
Proof. exact (EQ_MP (@lem1636845 n x h1 h2) (@lem0)). Qed.
Lemma lem1636847 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : term16 x n.
Proof. exact (@lem1636846 n x h1 h2 (@lem1636798 x n)). Qed.
Lemma lem1636848 (x : real) (h1 : term7 x) : term8 x.
Proof. exact (proj2 (@lem1636799 x h1)). Qed.
Lemma lem1636849 (x : real) (h1 : term7 x) : term9 x.
Proof. exact (proj1 (@lem1636799 x h1)). Qed.
Lemma lem1636850 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term8 x) = (term16 x n).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1636847 n x h1 h2) (fun h3 : term16 x n => @lem1636800 x h1)). Qed.
Lemma lem1636851 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : term16 x n.
Proof. exact (EQ_MP (@lem1636850 n x h1 h2) (@lem1636800 x h1)). Qed.
Lemma lem1636852 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : (term9 x) = (term16 x n).
Proof. exact (prop_ext (fun h3 : term9 x => @lem1636851 n x h1 h2) (fun h3 : term16 x n => @lem1636801 x h2)). Qed.
Lemma lem1636853 (n : nat) (x : real) (h1 : term8 x) (h2 : term9 x) : term16 x n.
Proof. exact (EQ_MP (@lem1636852 n x h1 h2) (@lem1636801 x h2)). Qed.
Lemma lem1636854 (n : nat) (x : real) (h1 : term7 x) (h2 : term9 x) : (term8 x) = (term16 x n).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1636853 n x h3 h2) (fun h3 : term16 x n => @lem1636848 x h1)). Qed.
Lemma lem1636855 (n : nat) (x : real) (h1 : term7 x) (h2 : term9 x) : term16 x n.
Proof. exact (EQ_MP (@lem1636854 n x h1 h2) (@lem1636848 x h1)). Qed.
Lemma lem1636856 (n : nat) (x : real) (h1 : term7 x) : (term9 x) = (term16 x n).
Proof. exact (prop_ext (fun h2 : term9 x => @lem1636855 n x h1 h2) (fun h2 : term16 x n => @lem1636849 x h1)). Qed.
Lemma lem1636857 (n : nat) (x : real) (h1 : term7 x) : term16 x n.
Proof. exact (EQ_MP (@lem1636856 n x h1) (@lem1636849 x h1)). Qed.
Lemma lem1636858 (x : real) (n : nat) : term22 x n.
Proof. exact (fun h0 : term7 x => @lem1636857 n x h0). Qed.
Lemma lem1636863 (n : nat) : term23 n.
Proof. exact (fun x : real => @lem1636858 x n). Qed.
Lemma lem1636868 : term24.
Proof. exact (fun n : nat => @lem1636863 n). Qed.
