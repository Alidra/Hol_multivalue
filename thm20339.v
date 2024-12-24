Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20339_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1804_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Lemma lem20272 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem20273 : (True = False) = False.
Proof. exact (@lem20272 False). Qed.
Lemma lem20274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20275 : term0 = (imp False).
Proof. exact (MK_COMB (@lem20274) (@lem20273)). Qed.
Lemma lem20278 (x : Prop) (x0 : Prop) : (x = x0) = (x = x0).
Proof. exact (eq_refl (x = x0)). Qed.
Lemma lem20279 (x : Prop) (x0 : Prop) : (term1 x x0) = (term2 x x0).
Proof. exact (MK_COMB (@lem20275) (@lem20278 x x0)). Qed.
Lemma lem20281 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem20282 (x : Prop) (x0 : Prop) : (term2 x x0) = True.
Proof. exact (@lem20281 (x = x0)). Qed.
Lemma lem20283 (x : Prop) (x0 : Prop) : (term1 x x0) = True.
Proof. exact (TRANS (@lem20279 x x0) (@lem20282 x x0)). Qed.
Lemma lem20284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20285 (x : Prop) (x0 : Prop) : (term3 x x0) = (and True).
Proof. exact (MK_COMB (@lem20284) (@lem20283 x x0)). Qed.
Lemma lem20287 {_739 : Type'} (x : _739) (p : Prop) : (term4 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem20288 (x : Prop) (p : Prop) : (term5 x p) = p.
Proof. exact (@lem20287 Prop x p). Qed.
Lemma lem20289 (x : Prop) (x1 : Prop) : (term6 x x1) = (x = x1).
Proof. exact (@lem20288 True (x = x1)). Qed.
Lemma lem20292 (x0 : Prop) (x : Prop) (x1 : Prop) : (term7 x0 x x1) = (term8 x x1).
Proof. exact (MK_COMB (@lem20285 x x0) (@lem20289 x x1)). Qed.
Lemma lem20294 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20295 (x : Prop) (x1 : Prop) : (term8 x x1) = (x = x1).
Proof. exact (@lem20294 (x = x1)). Qed.
Lemma lem20298 (x0 : Prop) (x : Prop) (x1 : Prop) : (term7 x0 x x1) = (x = x1).
Proof. exact (TRANS (@lem20292 x0 x x1) (@lem20295 x x1)). Qed.
Lemma lem20299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20300 (x0 : Prop) (x : Prop) (x1 : Prop) : (term9 x0 x x1) = (term10 x x1).
Proof. exact (MK_COMB (@lem20299) (@lem20298 x0 x x1)). Qed.
Lemma lem20306 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem20307 (x1 : Prop) : (True /\ x1) = x1.
Proof. exact (@lem20306 x1). Qed.
Lemma lem20308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem20309 (x1 : Prop) : (term11 x1) = (or x1).
Proof. exact (MK_COMB (@lem20308) (@lem20307 x1)). Qed.
Lemma lem20313 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20315 : term12 = (and False).
Proof. exact (MK_COMB (@lem20314) (@lem20313)). Qed.
Lemma lem20316 (x0 : Prop) : x0 = x0.
Proof. exact (eq_refl x0). Qed.
Lemma lem20317 (x0 : Prop) : (term13 x0) = (False /\ x0).
Proof. exact (MK_COMB (@lem20315) (@lem20316 x0)). Qed.
Lemma lem20319 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem20320 (x0 : Prop) : (False /\ x0) = False.
Proof. exact (@lem20319 x0). Qed.
Lemma lem20321 (x0 : Prop) : (term13 x0) = False.
Proof. exact (TRANS (@lem20317 x0) (@lem20320 x0)). Qed.
Lemma lem20322 (x0 : Prop) (x1 : Prop) : (term14 x1 x0) = (x1 \/ False).
Proof. exact (MK_COMB (@lem20309 x1) (@lem20321 x0)). Qed.
Lemma lem20324 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem20325 (x1 : Prop) : (x1 \/ False) = x1.
Proof. exact (@lem20324 x1). Qed.
Lemma lem20326 (x0 : Prop) (x1 : Prop) : (term14 x1 x0) = x1.
Proof. exact (TRANS (@lem20322 x0 x1) (@lem20325 x1)). Qed.
Lemma lem20327 (x : Prop) : (@eq Prop x) = (@eq Prop x).
Proof. exact (eq_refl (@eq Prop x)). Qed.
Lemma lem20328 (x0 : Prop) (x : Prop) (x1 : Prop) : (x = (term14 x1 x0)) = (x = x1).
Proof. exact (MK_COMB (@lem20327 x) (@lem20326 x0 x1)). Qed.
Lemma lem20331 (x0 : Prop) (x : Prop) (x1 : Prop) : (term15 x x1 x0) = (term16 x x1).
Proof. exact (MK_COMB (@lem20300 x0 x x1) (@lem20328 x0 x x1)). Qed.
Lemma lem20335 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem20336 (x : Prop) (x1 : Prop) : (term16 x x1) = True.
Proof. exact (@lem20335 (x = x1)). Qed.
Lemma lem20337 (x : Prop) (x1 : Prop) (x0 : Prop) : (term15 x x1 x0) = True.
Proof. exact (TRANS (@lem20331 x0 x x1) (@lem20336 x x1)). Qed.
Lemma lem20338 (x : Prop) (x1 : Prop) (x0 : Prop) : True = (term15 x x1 x0).
Proof. exact (SYM (@lem20337 x x1 x0)). Qed.
Lemma lem20339 (x : Prop) (x1 : Prop) (x0 : Prop) : term15 x x1 x0.
Proof. exact (EQ_MP (@lem20338 x x1 x0) (@lem0)). Qed.
