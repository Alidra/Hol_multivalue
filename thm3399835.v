Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3399835_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1855_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Lemma lem3399795 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term0 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3399796 {_88312 : Type'} (p : _88312 -> Prop) (x : _88312) : (term0 _88312 x p) = (p x).
Proof. exact (@lem3399795 _88312 p x). Qed.
Lemma lem3399797 {_88312 : Type'} (x : _88312) : (term1 _88312 x) = (term2 _88312 x).
Proof. exact (@lem3399796 _88312 (term3 _88312) x). Qed.
Lemma lem3399798 {_88312 : Type'} (x : _88312) : (term2 _88312 x) = True.
Proof. exact (eq_refl (term2 _88312 x)). Qed.
Lemma lem3399799 {_88312 : Type'} (GEN_PVAR_27 : _88312) : (@SETSPEC _88312 GEN_PVAR_27) = (@SETSPEC _88312 GEN_PVAR_27).
Proof. exact (eq_refl (@SETSPEC _88312 GEN_PVAR_27)). Qed.
Lemma lem3399800 {_88312 : Type'} (x : _88312) (GEN_PVAR_27 : _88312) : (term4 _88312 GEN_PVAR_27 x) = (@SETSPEC _88312 GEN_PVAR_27 True).
Proof. exact (MK_COMB (@lem3399799 _88312 GEN_PVAR_27) (@lem3399798 _88312 x)). Qed.
Lemma lem3399801 {_88312 : Type'} (x : _88312) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3399802 {_88312 : Type'} (GEN_PVAR_27 : _88312) (x : _88312) : (term5 _88312 GEN_PVAR_27 x) = (@SETSPEC _88312 GEN_PVAR_27 True x).
Proof. exact (MK_COMB (@lem3399800 _88312 x GEN_PVAR_27) (@lem3399801 _88312 x)). Qed.
Lemma lem3399803 {_88312 : Type'} (GEN_PVAR_27 : _88312) : (term6 _88312 GEN_PVAR_27) = (term7 _88312 GEN_PVAR_27).
Proof. exact (fun_ext (fun x : _88312 => @lem3399802 _88312 GEN_PVAR_27 x)). Qed.
Lemma lem3399804 {_88312 : Type'} : (@ex _88312) = (@ex _88312).
Proof. exact (eq_refl (@ex _88312)). Qed.
Lemma lem3399805 {_88312 : Type'} (GEN_PVAR_27 : _88312) : (term8 _88312 GEN_PVAR_27) = (term9 _88312 GEN_PVAR_27).
Proof. exact (MK_COMB (@lem3399804 _88312) (@lem3399803 _88312 GEN_PVAR_27)). Qed.
Lemma lem3399806 {_88312 : Type'} : (term10 _88312) = (term11 _88312).
Proof. exact (fun_ext (fun GEN_PVAR_27 : _88312 => @lem3399805 _88312 GEN_PVAR_27)). Qed.
Lemma lem3399807 {_88312 : Type'} : (@GSPEC _88312) = (@GSPEC _88312).
Proof. exact (eq_refl (@GSPEC _88312)). Qed.
Lemma lem3399808 {_88312 : Type'} : (term12 _88312) = (term13 _88312).
Proof. exact (MK_COMB (@lem3399807 _88312) (@lem3399806 _88312)). Qed.
Lemma lem3399809 {_88312 : Type'} (x : _88312) : (@IN _88312 x) = (@IN _88312 x).
Proof. exact (eq_refl (@IN _88312 x)). Qed.
Lemma lem3399810 {_88312 : Type'} (x : _88312) : (term1 _88312 x) = (term14 _88312 x).
Proof. exact (MK_COMB (@lem3399809 _88312 x) (@lem3399808 _88312)). Qed.
Lemma lem3399811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399812 {_88312 : Type'} (x : _88312) : (term15 _88312 x) = (term16 _88312 x).
Proof. exact (MK_COMB (@lem3399811) (@lem3399810 _88312 x)). Qed.
Lemma lem3399813 {_88312 : Type'} (x : _88312) : (term2 _88312 x) = True.
Proof. exact (eq_refl (term2 _88312 x)). Qed.
Lemma lem3399814 {_88312 : Type'} (x : _88312) : ((term1 _88312 x) = (term2 _88312 x)) = ((term14 _88312 x) = True).
Proof. exact (MK_COMB (@lem3399812 _88312 x) (@lem3399813 _88312 x)). Qed.
Lemma lem3399815 {_88312 : Type'} (x : _88312) : (term14 _88312 x) = True.
Proof. exact (EQ_MP (@lem3399814 _88312 x) (@lem3399797 _88312 x)). Qed.
Lemma lem3399816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399817 {_88312 : Type'} (x : _88312) : (term16 _88312 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3399816) (@lem3399815 _88312 x)). Qed.
Lemma lem3399819 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3399820 {_88312 : Type'} (x : _88312) : (@IN _88312 x (@UNIV _88312)) = True.
Proof. exact (@lem3399819 _88312 x). Qed.
Lemma lem3399821 {_88312 : Type'} (x : _88312) : ((term14 _88312 x) = (@IN _88312 x (@UNIV _88312))) = (True = True).
Proof. exact (MK_COMB (@lem3399817 _88312 x) (@lem3399820 _88312 x)). Qed.
Lemma lem3399823 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3399824 : (True = True) = True.
Proof. exact (@lem3399823 True). Qed.
Lemma lem3399825 {_88312 : Type'} (x : _88312) : ((term14 _88312 x) = (@IN _88312 x (@UNIV _88312))) = True.
Proof. exact (TRANS (@lem3399821 _88312 x) (@lem3399824)). Qed.
Lemma lem3399826 {_88312 : Type'} : (term17 _88312) = (term3 _88312).
Proof. exact (fun_ext (fun x : _88312 => @lem3399825 _88312 x)). Qed.
Lemma lem3399827 {_88312 : Type'} : (@all _88312) = (@all _88312).
Proof. exact (eq_refl (@all _88312)). Qed.
Lemma lem3399828 {_88312 : Type'} : (term18 _88312) = (term19 _88312).
Proof. exact (MK_COMB (@lem3399827 _88312) (@lem3399826 _88312)). Qed.
Lemma lem3399830 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3399831 {_88312 : Type'} (t : Prop) : (term20 _88312 t) = t.
Proof. exact (@lem3399830 _88312 t). Qed.
Lemma lem3399832 {_88312 : Type'} : (term19 _88312) = True.
Proof. exact (@lem3399831 _88312 True). Qed.
Lemma lem3399833 {_88312 : Type'} : (term18 _88312) = True.
Proof. exact (TRANS (@lem3399828 _88312) (@lem3399832 _88312)). Qed.
Lemma lem3399834 {_88312 : Type'} : True = (term18 _88312).
Proof. exact (SYM (@lem3399833 _88312)). Qed.
Lemma lem3399835 {_88312 : Type'} : term18 _88312.
Proof. exact (EQ_MP (@lem3399834 _88312) (@lem0)). Qed.
