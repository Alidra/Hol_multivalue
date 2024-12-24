Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXTENSION_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import IN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3181152 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem3181153 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem3181154 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem3181153 A B f) (@lem3181152 A B f)). Qed.
Lemma lem3181155 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem3181154 A B f g). Qed.
Lemma lem3181156 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem3181158 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (@lem3181151 A P). Qed.
Lemma lem3181159 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem3181160 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (EQ_MP (@lem3181159 A P) (@lem3181158 A P)). Qed.
Lemma lem3181161 {A : Type'} (P : A -> Prop) (x : A) : term6 A P x.
Proof. exact (@lem3181160 A P x). Qed.
Lemma lem3181162 {A : Type'} (P : A -> Prop) (x : A) : (term6 A P x) = ((@IN A x P) = (P x)).
Proof. exact (eq_refl (term6 A P x)). Qed.
Lemma lem3181179 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem3181156 A B f g) (@lem3181155 A B f g)). Qed.
Lemma lem3181180 {A : Type'} (f : A -> Prop) (g : A -> Prop) : (f = g) = (term7 A f g).
Proof. exact (@lem3181179 A Prop f g). Qed.
Lemma lem3181181 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (@lem3181180 A s t). Qed.
Lemma lem3181190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3181191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term9 A s t).
Proof. exact (MK_COMB (@lem3181190) (@lem3181181 A s t)). Qed.
Lemma lem3181201 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3181162 A P x) (@lem3181161 A P x)). Qed.
Lemma lem3181202 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3181201 A P x). Qed.
Lemma lem3181203 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3181202 A s x). Qed.
Lemma lem3181204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3181205 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3181204) (@lem3181203 A s x)). Qed.
Lemma lem3181207 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3181162 A P x) (@lem3181161 A P x)). Qed.
Lemma lem3181208 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3181207 A P x). Qed.
Lemma lem3181209 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3181208 A t x). Qed.
Lemma lem3181210 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3181205 A s x) (@lem3181209 A t x)). Qed.
Lemma lem3181215 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = (term13 A s t).
Proof. exact (fun_ext (fun x : A => @lem3181210 A s t x)). Qed.
Lemma lem3181216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3181217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3181216 A) (@lem3181215 A s t)). Qed.
Lemma lem3181222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term14 A s t)) = ((term7 A s t) = (term7 A s t)).
Proof. exact (MK_COMB (@lem3181191 A s t) (@lem3181217 A s t)). Qed.
Lemma lem3181224 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3181225 (x : Prop) : (x = x) = True.
Proof. exact (@lem3181224 Prop x). Qed.
Lemma lem3181226 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term7 A s t) = (term7 A s t)) = True.
Proof. exact (@lem3181225 (term7 A s t)). Qed.
Lemma lem3181227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term14 A s t)) = True.
Proof. exact (TRANS (@lem3181222 A s t) (@lem3181226 A s t)). Qed.
Lemma lem3181228 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3181227 A s t)). Qed.
Lemma lem3181229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3181230 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A).
Proof. exact (MK_COMB (@lem3181229 A) (@lem3181228 A s)). Qed.
Lemma lem3181232 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3181233 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem3181232 (A -> Prop) t). Qed.
Lemma lem3181234 {A : Type'} : (term18 A) = True.
Proof. exact (@lem3181233 A True). Qed.
Lemma lem3181235 {A : Type'} (s : A -> Prop) : (term17 A s) = True.
Proof. exact (TRANS (@lem3181230 A s) (@lem3181234 A)). Qed.
Lemma lem3181236 {A : Type'} : (term21 A) = (term16 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3181235 A s)). Qed.
Lemma lem3181237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3181238 {A : Type'} : (term22 A) = (term18 A).
Proof. exact (MK_COMB (@lem3181237 A) (@lem3181236 A)). Qed.
Lemma lem3181240 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3181241 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem3181240 (A -> Prop) t). Qed.
Lemma lem3181242 {A : Type'} : (term18 A) = True.
Proof. exact (@lem3181241 A True). Qed.
Lemma lem3181243 {A : Type'} : (term22 A) = True.
Proof. exact (TRANS (@lem3181238 A) (@lem3181242 A)). Qed.
Lemma lem3181244 {A : Type'} : True = (term22 A).
Proof. exact (SYM (@lem3181243 A)). Qed.
Lemma lem3181245 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3181244 A) (@lem0)). Qed.
