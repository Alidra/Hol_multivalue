Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_term_abbrevs.
Require Import ITERATE_EQ_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6938735 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6938737 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6938738 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem6938737 A B h1 op). Qed.
Lemma lem6938739 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6938740 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem6938739 A B op) (@lem6938738 A B op h1)). Qed.
Lemma lem6938741 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6938742 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6938740 A B op h1 (@lem6938741 B op h2)). Qed.
Lemma lem6938743 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem6938742 A B op h0 h1). Qed.
Lemma lem6938744 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6938745 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6938743 A B op h2 (@lem6938744 A B h1)). Qed.
Lemma lem6938746 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6938745 A B op h1 h0). Qed.
Lemma lem6938747 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem6938746 A B op h1). Qed.
Lemma lem6938748 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem6938747 A B h0). Qed.
Lemma lem6938749 {A B : Type'} : term0 A B.
Proof. exact (@lem6938748 A B (@lem5985778 A B)). Qed.
Lemma lem6938750 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem6938749 A B op). Qed.
Lemma lem6938751 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6938778 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6938779 {_127166 : Type'} : (@nsum _127166) = (@iterate nat _127166 Nat.add).
Proof. exact (@lem6938778 _127166). Qed.
Lemma lem6938780 {_127166 : Type'} (s : _127166 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6938781 {_127166 : Type'} (s : _127166 -> Prop) : (@nsum _127166 s) = (@iterate nat _127166 Nat.add s).
Proof. exact (MK_COMB (@lem6938779 _127166) (@lem6938780 _127166 s)). Qed.
Lemma lem6938782 {_127166 : Type'} (f : _127166 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6938783 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) : (@nsum _127166 s f) = (@iterate nat _127166 Nat.add s f).
Proof. exact (MK_COMB (@lem6938781 _127166 s) (@lem6938782 _127166 f)). Qed.
Lemma lem6938784 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6938785 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) : (term6 _127166 s f) = (term7 _127166 s f).
Proof. exact (MK_COMB (@lem6938784) (@lem6938783 _127166 s f)). Qed.
Lemma lem6938787 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6938788 {_127166 : Type'} : (@nsum _127166) = (@iterate nat _127166 Nat.add).
Proof. exact (@lem6938787 _127166). Qed.
Lemma lem6938789 {_127166 : Type'} (s : _127166 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6938790 {_127166 : Type'} (s : _127166 -> Prop) : (@nsum _127166 s) = (@iterate nat _127166 Nat.add s).
Proof. exact (MK_COMB (@lem6938788 _127166) (@lem6938789 _127166 s)). Qed.
Lemma lem6938791 {_127166 : Type'} (g : _127166 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6938792 {_127166 : Type'} (s : _127166 -> Prop) (g : _127166 -> nat) : (@nsum _127166 s g) = (@iterate nat _127166 Nat.add s g).
Proof. exact (MK_COMB (@lem6938790 _127166 s) (@lem6938791 _127166 g)). Qed.
Lemma lem6938793 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@iterate nat _127166 Nat.add s f) = (@iterate nat _127166 Nat.add s g)).
Proof. exact (MK_COMB (@lem6938785 _127166 s f) (@lem6938792 _127166 s g)). Qed.
Lemma lem6938796 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term8 _127166 s f g) = (term8 _127166 s f g).
Proof. exact (eq_refl (term8 _127166 s f g)). Qed.
Lemma lem6938797 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term9 _127166 f s g) = (term10 _127166 f s g).
Proof. exact (MK_COMB (@lem6938796 _127166 s f g) (@lem6938793 _127166 f s g)). Qed.
Lemma lem6938800 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term11 _127166 f g) = (term12 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem6938797 _127166 f s g)). Qed.
Lemma lem6938801 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem6938802 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term13 _127166 f g) = (term14 _127166 f g).
Proof. exact (MK_COMB (@lem6938801 _127166) (@lem6938800 _127166 f g)). Qed.
Lemma lem6938807 {_127166 : Type'} (f : _127166 -> nat) : (term15 _127166 f) = (term16 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem6938802 _127166 f g)). Qed.
Lemma lem6938808 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6938809 {_127166 : Type'} (f : _127166 -> nat) : (term17 _127166 f) = (term18 _127166 f).
Proof. exact (MK_COMB (@lem6938808 _127166) (@lem6938807 _127166 f)). Qed.
Lemma lem6938814 {_127166 : Type'} : (term19 _127166) = (term20 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem6938809 _127166 f)). Qed.
Lemma lem6938815 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem6938816 {_127166 : Type'} : (term21 _127166) = (term22 _127166).
Proof. exact (MK_COMB (@lem6938815 _127166) (@lem6938814 _127166)). Qed.
Lemma lem6938821 {_127166 : Type'} : (term22 _127166) = (term21 _127166).
Proof. exact (SYM (@lem6938816 _127166)). Qed.
Lemma lem6938823 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem6938751 A B op) (@lem6938750 A B op)). Qed.
Lemma lem6938824 {_127166 : Type'} (op : type1606) : term23 _127166 op.
Proof. exact (@lem6938823 _127166 nat op). Qed.
Lemma lem6938825 {_127166 : Type'} : term24 _127166.
Proof. exact (@lem6938824 _127166 Nat.add). Qed.
Lemma lem6938827 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6938735) (@lem6924403)). Qed.
Lemma lem6938828 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6938827)). Qed.
Lemma lem6938829 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6938828) (@lem0)). Qed.
Lemma lem6938830 {_127166 : Type'} : term22 _127166.
Proof. exact (@lem6938825 _127166 (@lem6938829)). Qed.
Lemma lem6938831 {_127166 : Type'} : term21 _127166.
Proof. exact (EQ_MP (@lem6938821 _127166) (@lem6938830 _127166)). Qed.
