Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIV_SUBSET_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3220216 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3220217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3220216 A s t). Qed.
Lemma lem3220218 {A : Type'} (s : A -> Prop) : (@SUBSET A (@UNIV A) s) = (term1 A s).
Proof. exact (@lem3220217 A (@UNIV A) s). Qed.
Lemma lem3220225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220226 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (MK_COMB (@lem3220225) (@lem3220218 A s)). Qed.
Lemma lem3220230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3220231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3220230 A s t). Qed.
Lemma lem3220232 {A : Type'} (s : A -> Prop) : (s = (@UNIV A)) = (term5 A s).
Proof. exact (@lem3220231 A s (@UNIV A)). Qed.
Lemma lem3220241 {A : Type'} (s : A -> Prop) : ((@SUBSET A (@UNIV A) s) = (s = (@UNIV A))) = ((term1 A s) = (term5 A s)).
Proof. exact (MK_COMB (@lem3220226 A s) (@lem3220232 A s)). Qed.
Lemma lem3220246 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3220241 A s)). Qed.
Lemma lem3220247 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3220248 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem3220247 A) (@lem3220246 A)). Qed.
Lemma lem3220253 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3220248 A)). Qed.
Lemma lem3220267 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3220268 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3220267 A x). Qed.
Lemma lem3220269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3220270 {A : Type'} (x : A) : (term10 A x) = (imp True).
Proof. exact (MK_COMB (@lem3220269) (@lem3220268 A x)). Qed.
Lemma lem3220272 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220273 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3220272 A P x). Qed.
Lemma lem3220274 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3220273 A s x). Qed.
Lemma lem3220275 {A : Type'} (s : A -> Prop) (x : A) : (term11 A x s) = (term12 A s x).
Proof. exact (MK_COMB (@lem3220270 A x) (@lem3220274 A s x)). Qed.
Lemma lem3220277 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3220278 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (s x).
Proof. exact (@lem3220277 (s x)). Qed.
Lemma lem3220279 {A : Type'} (s : A -> Prop) (x : A) : (term11 A x s) = (s x).
Proof. exact (TRANS (@lem3220275 A s x) (@lem3220278 A s x)). Qed.
Lemma lem3220280 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (fun_ext (fun x : A => @lem3220279 A s x)). Qed.
Lemma lem3220281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3220282 {A : Type'} (s : A -> Prop) : (term1 A s) = (term15 A s).
Proof. exact (MK_COMB (@lem3220281 A) (@lem3220280 A s)). Qed.
Lemma lem3220287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220288 {A : Type'} (s : A -> Prop) : (term3 A s) = (term16 A s).
Proof. exact (MK_COMB (@lem3220287) (@lem3220282 A s)). Qed.
Lemma lem3220296 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3220297 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3220296 A P x). Qed.
Lemma lem3220298 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3220297 A s x). Qed.
Lemma lem3220299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3220300 {A : Type'} (s : A -> Prop) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (MK_COMB (@lem3220299) (@lem3220298 A s x)). Qed.
Lemma lem3220302 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3220303 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3220302 A x). Qed.
Lemma lem3220304 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = ((s x) = True).
Proof. exact (MK_COMB (@lem3220300 A s x) (@lem3220303 A x)). Qed.
Lemma lem3220306 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3220307 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = True) = (s x).
Proof. exact (@lem3220306 (s x)). Qed.
Lemma lem3220308 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = (s x).
Proof. exact (TRANS (@lem3220304 A s x) (@lem3220307 A s x)). Qed.
Lemma lem3220309 {A : Type'} (s : A -> Prop) : (term19 A s) = (term14 A s).
Proof. exact (fun_ext (fun x : A => @lem3220308 A s x)). Qed.
Lemma lem3220310 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3220311 {A : Type'} (s : A -> Prop) : (term5 A s) = (term15 A s).
Proof. exact (MK_COMB (@lem3220310 A) (@lem3220309 A s)). Qed.
Lemma lem3220316 {A : Type'} (s : A -> Prop) : ((term1 A s) = (term5 A s)) = ((term15 A s) = (term15 A s)).
Proof. exact (MK_COMB (@lem3220288 A s) (@lem3220311 A s)). Qed.
Lemma lem3220318 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3220319 (x : Prop) : (x = x) = True.
Proof. exact (@lem3220318 Prop x). Qed.
Lemma lem3220320 {A : Type'} (s : A -> Prop) : ((term15 A s) = (term15 A s)) = True.
Proof. exact (@lem3220319 (term15 A s)). Qed.
Lemma lem3220321 {A : Type'} (s : A -> Prop) : ((term1 A s) = (term5 A s)) = True.
Proof. exact (TRANS (@lem3220316 A s) (@lem3220320 A s)). Qed.
Lemma lem3220322 {A : Type'} : (term7 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3220321 A s)). Qed.
Lemma lem3220323 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3220324 {A : Type'} : (term9 A) = (term21 A).
Proof. exact (MK_COMB (@lem3220323 A) (@lem3220322 A)). Qed.
Lemma lem3220326 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3220327 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (@lem3220326 (A -> Prop) t). Qed.
Lemma lem3220328 {A : Type'} : (term21 A) = True.
Proof. exact (@lem3220327 A True). Qed.
Lemma lem3220329 {A : Type'} : (term9 A) = True.
Proof. exact (TRANS (@lem3220324 A) (@lem3220328 A)). Qed.
Lemma lem3220330 {A : Type'} : True = (term9 A).
Proof. exact (SYM (@lem3220329 A)). Qed.
Lemma lem3220331 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3220330 A) (@lem0)). Qed.
Lemma lem3220332 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3220253 A) (@lem3220331 A)). Qed.
