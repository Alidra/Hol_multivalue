Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3220137 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3220138 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3220137 A s t). Qed.
Lemma lem3220139 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = (term1 A s).
Proof. exact (@lem3220138 A s (@UNIV A)). Qed.
Lemma lem3220146 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3220139 A s)). Qed.
Lemma lem3220147 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3220148 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3220147 A) (@lem3220146 A)). Qed.
Lemma lem3220153 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3220148 A)). Qed.
Lemma lem3220165 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220166 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3220165 A P x). Qed.
Lemma lem3220167 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3220166 A s x). Qed.
Lemma lem3220168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3220169 {A : Type'} (s : A -> Prop) (x : A) : (term6 A x s) = (term7 A s x).
Proof. exact (MK_COMB (@lem3220168) (@lem3220167 A s x)). Qed.
Lemma lem3220171 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3220172 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3220171 A x). Qed.
Lemma lem3220173 {A : Type'} (s : A -> Prop) (x : A) : (term8 A s x) = (term9 A s x).
Proof. exact (MK_COMB (@lem3220169 A s x) (@lem3220172 A x)). Qed.
Lemma lem3220175 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3220176 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = True.
Proof. exact (@lem3220175 (s x)). Qed.
Lemma lem3220177 {A : Type'} (s : A -> Prop) (x : A) : (term8 A s x) = True.
Proof. exact (TRANS (@lem3220173 A s x) (@lem3220176 A s x)). Qed.
Lemma lem3220178 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A).
Proof. exact (fun_ext (fun x : A => @lem3220177 A s x)). Qed.
Lemma lem3220179 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3220180 {A : Type'} (s : A -> Prop) : (term1 A s) = (term12 A).
Proof. exact (MK_COMB (@lem3220179 A) (@lem3220178 A s)). Qed.
Lemma lem3220182 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3220183 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (@lem3220182 A t). Qed.
Lemma lem3220184 {A : Type'} : (term12 A) = True.
Proof. exact (@lem3220183 A True). Qed.
Lemma lem3220185 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3220180 A s) (@lem3220184 A)). Qed.
Lemma lem3220186 {A : Type'} : (term3 A) = (term14 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3220185 A s)). Qed.
Lemma lem3220187 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3220188 {A : Type'} : (term5 A) = (term15 A).
Proof. exact (MK_COMB (@lem3220187 A) (@lem3220186 A)). Qed.
Lemma lem3220190 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3220191 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (@lem3220190 (A -> Prop) t). Qed.
Lemma lem3220192 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3220191 A True). Qed.
Lemma lem3220193 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3220188 A) (@lem3220192 A)). Qed.
Lemma lem3220194 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3220193 A)). Qed.
Lemma lem3220195 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3220194 A) (@lem0)). Qed.
Lemma lem3220196 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3220153 A) (@lem3220195 A)). Qed.
