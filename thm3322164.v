Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3322164_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem3322109 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3322110 {_86801 : Type'} (s : type686 _86801) (x : _86801) : (term0 _86801 x s) = (term1 _86801 s x).
Proof. exact (@lem3322109 _86801 s x). Qed.
Lemma lem3322111 {_86801 : Type'} (x : _86801) : (term2 _86801 x) = (term3 _86801 x).
Proof. exact (@lem3322110 _86801 (@EMPTY (_86801 -> Prop)) x). Qed.
Lemma lem3322119 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3322120 {_86801 : Type'} (x : _86801 -> Prop) : (@IN (_86801 -> Prop) x (@EMPTY (_86801 -> Prop))) = False.
Proof. exact (@lem3322119 (_86801 -> Prop) x). Qed.
Lemma lem3322121 {_86801 : Type'} (t : _86801 -> Prop) : (@IN (_86801 -> Prop) t (@EMPTY (_86801 -> Prop))) = False.
Proof. exact (@lem3322120 _86801 t). Qed.
Lemma lem3322122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322123 {_86801 : Type'} (t : _86801 -> Prop) : (term4 _86801 t) = (and False).
Proof. exact (MK_COMB (@lem3322122) (@lem3322121 _86801 t)). Qed.
Lemma lem3322125 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3322126 {_86801 : Type'} (P : _86801 -> Prop) (x : _86801) : (@IN _86801 x P) = (P x).
Proof. exact (@lem3322125 _86801 P x). Qed.
Lemma lem3322127 {_86801 : Type'} (t : _86801 -> Prop) (x : _86801) : (@IN _86801 x t) = (t x).
Proof. exact (@lem3322126 _86801 t x). Qed.
Lemma lem3322128 {_86801 : Type'} (t : _86801 -> Prop) (x : _86801) : (term5 _86801 x t) = (term6 _86801 t x).
Proof. exact (MK_COMB (@lem3322123 _86801 t) (@lem3322127 _86801 t x)). Qed.
Lemma lem3322130 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3322131 {_86801 : Type'} (t : _86801 -> Prop) (x : _86801) : (term6 _86801 t x) = False.
Proof. exact (@lem3322130 (t x)). Qed.
Lemma lem3322132 {_86801 : Type'} (x : _86801) (t : _86801 -> Prop) : (term5 _86801 x t) = False.
Proof. exact (TRANS (@lem3322128 _86801 t x) (@lem3322131 _86801 t x)). Qed.
Lemma lem3322133 {_86801 : Type'} (x : _86801) : (term7 _86801 x) = (term8 _86801).
Proof. exact (fun_ext (fun t : _86801 -> Prop => @lem3322132 _86801 x t)). Qed.
Lemma lem3322134 {_86801 : Type'} : (@ex (_86801 -> Prop)) = (@ex (_86801 -> Prop)).
Proof. exact (eq_refl (@ex (_86801 -> Prop))). Qed.
Lemma lem3322135 {_86801 : Type'} (x : _86801) : (term3 _86801 x) = (term9 _86801).
Proof. exact (MK_COMB (@lem3322134 _86801) (@lem3322133 _86801 x)). Qed.
Lemma lem3322137 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem3322138 {_86801 : Type'} (t : Prop) : (term11 _86801 t) = t.
Proof. exact (@lem3322137 (_86801 -> Prop) t). Qed.
Lemma lem3322139 {_86801 : Type'} : (term9 _86801) = False.
Proof. exact (@lem3322138 _86801 False). Qed.
Lemma lem3322140 {_86801 : Type'} (x : _86801) : (term3 _86801 x) = False.
Proof. exact (TRANS (@lem3322135 _86801 x) (@lem3322139 _86801)). Qed.
Lemma lem3322141 {_86801 : Type'} (x : _86801) : (term2 _86801 x) = False.
Proof. exact (TRANS (@lem3322111 _86801 x) (@lem3322140 _86801 x)). Qed.
Lemma lem3322142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322143 {_86801 : Type'} (x : _86801) : (term12 _86801 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3322142) (@lem3322141 _86801 x)). Qed.
Lemma lem3322145 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3322146 {_86801 : Type'} (x : _86801) : (@IN _86801 x (@EMPTY _86801)) = False.
Proof. exact (@lem3322145 _86801 x). Qed.
Lemma lem3322147 {_86801 : Type'} (x : _86801) : ((term2 _86801 x) = (@IN _86801 x (@EMPTY _86801))) = (False = False).
Proof. exact (MK_COMB (@lem3322143 _86801 x) (@lem3322146 _86801 x)). Qed.
Lemma lem3322149 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3322150 : (False = False) = (~ False).
Proof. exact (@lem3322149 False). Qed.
Lemma lem3322152 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3322153 : (False = False) = True.
Proof. exact (TRANS (@lem3322150) (@lem3322152)). Qed.
Lemma lem3322154 {_86801 : Type'} (x : _86801) : ((term2 _86801 x) = (@IN _86801 x (@EMPTY _86801))) = True.
Proof. exact (TRANS (@lem3322147 _86801 x) (@lem3322153)). Qed.
Lemma lem3322155 {_86801 : Type'} : (term13 _86801) = (term14 _86801).
Proof. exact (fun_ext (fun x : _86801 => @lem3322154 _86801 x)). Qed.
Lemma lem3322156 {_86801 : Type'} : (@all _86801) = (@all _86801).
Proof. exact (eq_refl (@all _86801)). Qed.
Lemma lem3322157 {_86801 : Type'} : (term15 _86801) = (term16 _86801).
Proof. exact (MK_COMB (@lem3322156 _86801) (@lem3322155 _86801)). Qed.
Lemma lem3322159 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3322160 {_86801 : Type'} (t : Prop) : (term17 _86801 t) = t.
Proof. exact (@lem3322159 _86801 t). Qed.
Lemma lem3322161 {_86801 : Type'} : (term16 _86801) = True.
Proof. exact (@lem3322160 _86801 True). Qed.
Lemma lem3322162 {_86801 : Type'} : (term15 _86801) = True.
Proof. exact (TRANS (@lem3322157 _86801) (@lem3322161 _86801)). Qed.
Lemma lem3322163 {_86801 : Type'} : True = (term15 _86801).
Proof. exact (SYM (@lem3322162 _86801)). Qed.
Lemma lem3322164 {_86801 : Type'} : term15 _86801.
Proof. exact (EQ_MP (@lem3322163 _86801) (@lem0)). Qed.
