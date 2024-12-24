Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3399757_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1857_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem3399714 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term0 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3399715 {_88295 : Type'} (p : _88295 -> Prop) (x : _88295) : (term0 _88295 x p) = (p x).
Proof. exact (@lem3399714 _88295 p x). Qed.
Lemma lem3399716 {_88295 : Type'} (x : _88295) : (term1 _88295 x) = (term2 _88295 x).
Proof. exact (@lem3399715 _88295 (term3 _88295) x). Qed.
Lemma lem3399717 {_88295 : Type'} (x : _88295) : (term2 _88295 x) = False.
Proof. exact (eq_refl (term2 _88295 x)). Qed.
Lemma lem3399718 {_88295 : Type'} (GEN_PVAR_26 : _88295) : (@SETSPEC _88295 GEN_PVAR_26) = (@SETSPEC _88295 GEN_PVAR_26).
Proof. exact (eq_refl (@SETSPEC _88295 GEN_PVAR_26)). Qed.
Lemma lem3399719 {_88295 : Type'} (x : _88295) (GEN_PVAR_26 : _88295) : (term4 _88295 GEN_PVAR_26 x) = (@SETSPEC _88295 GEN_PVAR_26 False).
Proof. exact (MK_COMB (@lem3399718 _88295 GEN_PVAR_26) (@lem3399717 _88295 x)). Qed.
Lemma lem3399720 {_88295 : Type'} (x : _88295) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3399721 {_88295 : Type'} (GEN_PVAR_26 : _88295) (x : _88295) : (term5 _88295 GEN_PVAR_26 x) = (@SETSPEC _88295 GEN_PVAR_26 False x).
Proof. exact (MK_COMB (@lem3399719 _88295 x GEN_PVAR_26) (@lem3399720 _88295 x)). Qed.
Lemma lem3399722 {_88295 : Type'} (GEN_PVAR_26 : _88295) : (term6 _88295 GEN_PVAR_26) = (term7 _88295 GEN_PVAR_26).
Proof. exact (fun_ext (fun x : _88295 => @lem3399721 _88295 GEN_PVAR_26 x)). Qed.
Lemma lem3399723 {_88295 : Type'} : (@ex _88295) = (@ex _88295).
Proof. exact (eq_refl (@ex _88295)). Qed.
Lemma lem3399724 {_88295 : Type'} (GEN_PVAR_26 : _88295) : (term8 _88295 GEN_PVAR_26) = (term9 _88295 GEN_PVAR_26).
Proof. exact (MK_COMB (@lem3399723 _88295) (@lem3399722 _88295 GEN_PVAR_26)). Qed.
Lemma lem3399725 {_88295 : Type'} : (term10 _88295) = (term11 _88295).
Proof. exact (fun_ext (fun GEN_PVAR_26 : _88295 => @lem3399724 _88295 GEN_PVAR_26)). Qed.
Lemma lem3399726 {_88295 : Type'} : (@GSPEC _88295) = (@GSPEC _88295).
Proof. exact (eq_refl (@GSPEC _88295)). Qed.
Lemma lem3399727 {_88295 : Type'} : (term12 _88295) = (term13 _88295).
Proof. exact (MK_COMB (@lem3399726 _88295) (@lem3399725 _88295)). Qed.
Lemma lem3399728 {_88295 : Type'} (x : _88295) : (@IN _88295 x) = (@IN _88295 x).
Proof. exact (eq_refl (@IN _88295 x)). Qed.
Lemma lem3399729 {_88295 : Type'} (x : _88295) : (term1 _88295 x) = (term14 _88295 x).
Proof. exact (MK_COMB (@lem3399728 _88295 x) (@lem3399727 _88295)). Qed.
Lemma lem3399730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399731 {_88295 : Type'} (x : _88295) : (term15 _88295 x) = (term16 _88295 x).
Proof. exact (MK_COMB (@lem3399730) (@lem3399729 _88295 x)). Qed.
Lemma lem3399732 {_88295 : Type'} (x : _88295) : (term2 _88295 x) = False.
Proof. exact (eq_refl (term2 _88295 x)). Qed.
Lemma lem3399733 {_88295 : Type'} (x : _88295) : ((term1 _88295 x) = (term2 _88295 x)) = ((term14 _88295 x) = False).
Proof. exact (MK_COMB (@lem3399731 _88295 x) (@lem3399732 _88295 x)). Qed.
Lemma lem3399734 {_88295 : Type'} (x : _88295) : (term14 _88295 x) = False.
Proof. exact (EQ_MP (@lem3399733 _88295 x) (@lem3399716 _88295 x)). Qed.
Lemma lem3399735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399736 {_88295 : Type'} (x : _88295) : (term16 _88295 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3399735) (@lem3399734 _88295 x)). Qed.
Lemma lem3399738 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3399739 {_88295 : Type'} (x : _88295) : (@IN _88295 x (@EMPTY _88295)) = False.
Proof. exact (@lem3399738 _88295 x). Qed.
Lemma lem3399740 {_88295 : Type'} (x : _88295) : ((term14 _88295 x) = (@IN _88295 x (@EMPTY _88295))) = (False = False).
Proof. exact (MK_COMB (@lem3399736 _88295 x) (@lem3399739 _88295 x)). Qed.
Lemma lem3399742 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3399743 : (False = False) = (~ False).
Proof. exact (@lem3399742 False). Qed.
Lemma lem3399745 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3399746 : (False = False) = True.
Proof. exact (TRANS (@lem3399743) (@lem3399745)). Qed.
Lemma lem3399747 {_88295 : Type'} (x : _88295) : ((term14 _88295 x) = (@IN _88295 x (@EMPTY _88295))) = True.
Proof. exact (TRANS (@lem3399740 _88295 x) (@lem3399746)). Qed.
Lemma lem3399748 {_88295 : Type'} : (term17 _88295) = (term18 _88295).
Proof. exact (fun_ext (fun x : _88295 => @lem3399747 _88295 x)). Qed.
Lemma lem3399749 {_88295 : Type'} : (@all _88295) = (@all _88295).
Proof. exact (eq_refl (@all _88295)). Qed.
Lemma lem3399750 {_88295 : Type'} : (term19 _88295) = (term20 _88295).
Proof. exact (MK_COMB (@lem3399749 _88295) (@lem3399748 _88295)). Qed.
Lemma lem3399752 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3399753 {_88295 : Type'} (t : Prop) : (term21 _88295 t) = t.
Proof. exact (@lem3399752 _88295 t). Qed.
Lemma lem3399754 {_88295 : Type'} : (term20 _88295) = True.
Proof. exact (@lem3399753 _88295 True). Qed.
Lemma lem3399755 {_88295 : Type'} : (term19 _88295) = True.
Proof. exact (TRANS (@lem3399750 _88295) (@lem3399754 _88295)). Qed.
Lemma lem3399756 {_88295 : Type'} : True = (term19 _88295).
Proof. exact (SYM (@lem3399755 _88295)). Qed.
Lemma lem3399757 {_88295 : Type'} : term19 _88295.
Proof. exact (EQ_MP (@lem3399756 _88295) (@lem0)). Qed.
