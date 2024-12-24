Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_EMPTY_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3269140 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3269141 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3269140 A s t). Qed.
Lemma lem3269142 {A : Type'} (s : A -> Prop) : ((@DIFF A s (@EMPTY A)) = s) = (term1 A s).
Proof. exact (@lem3269141 A (@DIFF A s (@EMPTY A)) s). Qed.
Lemma lem3269151 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269142 A s)). Qed.
Lemma lem3269152 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269153 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3269152 A) (@lem3269151 A)). Qed.
Lemma lem3269158 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3269153 A)). Qed.
Lemma lem3269170 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3269171 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (@lem3269170 A s x t). Qed.
Lemma lem3269172 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (term9 A s x).
Proof. exact (@lem3269171 A s x (@EMPTY A)). Qed.
Lemma lem3269176 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269177 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269176 A P x). Qed.
Lemma lem3269178 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3269177 A s x). Qed.
Lemma lem3269179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269180 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3269179) (@lem3269178 A s x)). Qed.
Lemma lem3269182 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3269183 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3269182 A x). Qed.
Lemma lem3269184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3269185 {A : Type'} (x : A) : (term12 A x) = (~ False).
Proof. exact (MK_COMB (@lem3269184) (@lem3269183 A x)). Qed.
Lemma lem3269187 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3269188 {A : Type'} (x : A) : (term12 A x) = True.
Proof. exact (TRANS (@lem3269185 A x) (@lem3269187)). Qed.
Lemma lem3269189 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = (term13 A s x).
Proof. exact (MK_COMB (@lem3269180 A s x) (@lem3269188 A x)). Qed.
Lemma lem3269191 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3269192 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (s x).
Proof. exact (@lem3269191 (s x)). Qed.
Lemma lem3269193 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = (s x).
Proof. exact (TRANS (@lem3269189 A s x) (@lem3269192 A s x)). Qed.
Lemma lem3269194 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (s x).
Proof. exact (TRANS (@lem3269172 A s x) (@lem3269193 A s x)). Qed.
Lemma lem3269195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3269196 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term15 A s x).
Proof. exact (MK_COMB (@lem3269195) (@lem3269194 A s x)). Qed.
Lemma lem3269198 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269199 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269198 A P x). Qed.
Lemma lem3269200 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3269199 A s x). Qed.
Lemma lem3269201 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3269196 A s x) (@lem3269200 A s x)). Qed.
Lemma lem3269203 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3269204 (x : Prop) : (x = x) = True.
Proof. exact (@lem3269203 Prop x). Qed.
Lemma lem3269205 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3269204 (s x)). Qed.
Lemma lem3269206 {A : Type'} (x : A) (s : A -> Prop) : ((term8 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3269201 A s x) (@lem3269205 A s x)). Qed.
Lemma lem3269207 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A).
Proof. exact (fun_ext (fun x : A => @lem3269206 A x s)). Qed.
Lemma lem3269208 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3269209 {A : Type'} (s : A -> Prop) : (term1 A s) = (term18 A).
Proof. exact (MK_COMB (@lem3269208 A) (@lem3269207 A s)). Qed.
Lemma lem3269211 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3269212 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (@lem3269211 A t). Qed.
Lemma lem3269213 {A : Type'} : (term18 A) = True.
Proof. exact (@lem3269212 A True). Qed.
Lemma lem3269214 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3269209 A s) (@lem3269213 A)). Qed.
Lemma lem3269215 {A : Type'} : (term3 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269214 A s)). Qed.
Lemma lem3269216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269217 {A : Type'} : (term5 A) = (term21 A).
Proof. exact (MK_COMB (@lem3269216 A) (@lem3269215 A)). Qed.
Lemma lem3269219 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3269220 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (@lem3269219 (A -> Prop) t). Qed.
Lemma lem3269221 {A : Type'} : (term21 A) = True.
Proof. exact (@lem3269220 A True). Qed.
Lemma lem3269222 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3269217 A) (@lem3269221 A)). Qed.
Lemma lem3269223 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3269222 A)). Qed.
Lemma lem3269224 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3269223 A) (@lem0)). Qed.
Lemma lem3269225 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3269158 A) (@lem3269224 A)). Qed.
