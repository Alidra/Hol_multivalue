Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_FUN_term_abbrevs.
Require Import FINITE_RULES_spec.
Require Import FINITE_SUBSET_spec.
Require Import FINREC_EXISTS_LEMMA_spec.
Require Import FINREC_FUN_LEMMA_spec.
Require Import FINREC_SUC_LEMMA_spec.
Require Import FINREC_UNIQUE_LEMMA_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3791009_spec.
Require Import thm3791010_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem3811205 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3811206 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3811205 A h1 s). Qed.
Lemma lem3811207 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3811208 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3811207 A s) (@lem3811206 A s h1)). Qed.
Lemma lem3811209 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3811208 A s h1 t). Qed.
Lemma lem3811210 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3811211 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3811210 A t s) (@lem3811209 A s t h1)). Qed.
Lemma lem3811212 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3811213 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3811211 A t s h1 (@lem3811212 A s t h2)). Qed.
Lemma lem3811214 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3811213 A s t h0 h1). Qed.
Lemma lem3811215 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3811216 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3811215 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3811214 A s t h0)). Qed.
Lemma lem3811217 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3811218 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3811216 A s h2 (@lem3811217 A h1)). Qed.
Lemma lem3811219 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3811218 A s h1 h0). Qed.
Lemma lem3811220 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3811219 A s h1). Qed.
Lemma lem3811221 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3811220 A h0). Qed.
Lemma lem3811222 {A : Type'} : term10 A.
Proof. exact (@lem3811221 A (@lem3599924 A)). Qed.
Lemma lem3811223 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3811222 A s). Qed.
Lemma lem3811224 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3811226 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem3811227 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (eq_refl (term13 A P)). Qed.
Lemma lem3811228 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (EQ_MP (@lem3811227 A P) (@lem3811226 A P)). Qed.
Lemma lem3811229 {A : Type'} (P : A -> Prop) (Q : Prop) : term15 A P Q.
Proof. exact (@lem3811228 A P Q). Qed.
Lemma lem3811230 {A : Type'} (P : A -> Prop) (Q : Prop) : (term15 A P Q) = ((term16 A P Q) = (term17 A P Q)).
Proof. exact (eq_refl (term15 A P Q)). Qed.
Lemma lem3811232 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3811244 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3811245 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3811247 {A B C : Type'} (P : A -> Prop) : term18 A B C P.
Proof. exact (@lem3811194 A B C P). Qed.
Lemma lem3811248 {A B C : Type'} (P : A -> Prop) : (term18 A B C P) = (term19 A B C P).
Proof. exact (eq_refl (term18 A B C P)). Qed.
Lemma lem3811249 {A B C : Type'} (P : A -> Prop) : term19 A B C P.
Proof. exact (EQ_MP (@lem3811248 A B C P) (@lem3811247 A B C P)). Qed.
Lemma lem3811250 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : term20 A B C P R.
Proof. exact (@lem3811249 A B C P R). Qed.
Lemma lem3811251 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : (term20 A B C P R) = (term21 A B C P R).
Proof. exact (eq_refl (term20 A B C P R)). Qed.
Lemma lem3811253 {A B : Type'} (f : type1411 A B) : term22 A B f.
Proof. exact (@lem3808349 A B f). Qed.
Lemma lem3811254 {A B : Type'} (f : type1411 A B) : (term22 A B f) = (term23 A B f).
Proof. exact (eq_refl (term22 A B f)). Qed.
Lemma lem3811255 {A B : Type'} (f : type1411 A B) : term23 A B f.
Proof. exact (EQ_MP (@lem3811254 A B f) (@lem3811253 A B f)). Qed.
Lemma lem3811256 {A B : Type'} (f : type1411 A B) (b : B) : term24 A B f b.
Proof. exact (@lem3811255 A B f b). Qed.
Lemma lem3811257 {A B : Type'} (f : type1411 A B) (b : B) : (term24 A B f b) = (term25 A B f b).
Proof. exact (eq_refl (term24 A B f b)). Qed.
Lemma lem3811258 {A B : Type'} (f : type1411 A B) (b : B) : term25 A B f b.
Proof. exact (EQ_MP (@lem3811257 A B f b) (@lem3811256 A B f b)). Qed.
Lemma lem3811259 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term26 A B f.
Proof. exact (h1). Qed.
Lemma lem3811260 {A B : Type'} (h1 : term27 A B) : term27 A B.
Proof. exact (h1). Qed.
Lemma lem3811261 {A B : Type'} (f : type1411 A B) (h1 : term27 A B) : term28 A B f.
Proof. exact (@lem3811260 A B h1 f). Qed.
Lemma lem3811262 {A B : Type'} (f : type1411 A B) : (term28 A B f) = (term29 A B f).
Proof. exact (eq_refl (term28 A B f)). Qed.
Lemma lem3811263 {A B : Type'} (f : type1411 A B) (h1 : term27 A B) : term29 A B f.
Proof. exact (EQ_MP (@lem3811262 A B f) (@lem3811261 A B f h1)). Qed.
Lemma lem3811264 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term27 A B) : term30 A B f b.
Proof. exact (@lem3811263 A B f h1 b). Qed.
Lemma lem3811265 {A B : Type'} (f : type1411 A B) (b : B) : (term30 A B f b) = (term31 A B f b).
Proof. exact (eq_refl (term30 A B f b)). Qed.
Lemma lem3811266 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term27 A B) : term31 A B f b.
Proof. exact (EQ_MP (@lem3811265 A B f b) (@lem3811264 A B f b h1)). Qed.
Lemma lem3811267 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term26 A B f.
Proof. exact (h1). Qed.
Lemma lem3811268 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) (h2 : term27 A B) : term32 A B f b.
Proof. exact (@lem3811266 A B f b h2 (@lem3811267 A B f h1)). Qed.
Lemma lem3811269 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) (h2 : term27 A B) : term33 A B f.
Proof. exact (fun b : B => @lem3811268 A B b f h1 h2). Qed.
Lemma lem3811270 {A B : Type'} (f : type1411 A B) (h1 : term27 A B) : term34 A B f.
Proof. exact (fun h0 : term26 A B f => @lem3811269 A B f h0 h1). Qed.
Lemma lem3811271 {A B : Type'} (h1 : term27 A B) : term35 A B.
Proof. exact (fun f : type1411 A B => @lem3811270 A B f h1). Qed.
Lemma lem3811272 {A B : Type'} : term36 A B.
Proof. exact (fun h0 : term27 A B => @lem3811271 A B h0). Qed.
Lemma lem3811273 {A B : Type'} : term35 A B.
Proof. exact (@lem3811272 A B (@lem3807377 A B)). Qed.
Lemma lem3811274 {A B : Type'} (f : type1411 A B) : term37 A B f.
Proof. exact (@lem3811273 A B f). Qed.
Lemma lem3811275 {A B : Type'} (f : type1411 A B) : (term37 A B f) = (term34 A B f).
Proof. exact (eq_refl (term37 A B f)). Qed.
Lemma lem3811278 {A B : Type'} (f : type1411 A B) : term34 A B f.
Proof. exact (EQ_MP (@lem3811275 A B f) (@lem3811274 A B f)). Qed.
Lemma lem3811279 {A B : Type'} (f : type1411 A B) : term34 A B f.
Proof. exact (@lem3811278 A B f). Qed.
Lemma lem3811280 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term33 A B f.
Proof. exact (@lem3811279 A B f (@lem3811259 A B f h1)). Qed.
Lemma lem3811281 {A B : Type'} (f : type1411 A B) (h1 : term33 A B f) : term33 A B f.
Proof. exact (h1). Qed.
Lemma lem3811282 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term33 A B f) : term38 A B f b.
Proof. exact (@lem3811281 A B f h1 b). Qed.
Lemma lem3811283 {A B : Type'} (f : type1411 A B) (b : B) : (term38 A B f b) = (term32 A B f b).
Proof. exact (eq_refl (term38 A B f b)). Qed.
Lemma lem3811284 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term33 A B f) : term32 A B f b.
Proof. exact (EQ_MP (@lem3811283 A B f b) (@lem3811282 A B b f h1)). Qed.
Lemma lem3811285 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term32 A B f b) : term32 A B f b.
Proof. exact (h1). Qed.
Lemma lem3811286 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term32 A B f b) : term39 A B f b.
Proof. exact (conj (@lem3811258 A B f b) (@lem3811285 A B f b h1)). Qed.
Lemma lem3811287 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term39 A B f b) : term39 A B f b.
Proof. exact (h1). Qed.
Lemma lem3811289 {A B C : Type'} (P : A -> Prop) (R : type1408 A B C) : term21 A B C P R.
Proof. exact (EQ_MP (@lem3811251 A B C P R) (@lem3811250 A B C P R)). Qed.
Lemma lem3811290 {A B : Type'} (P : type686 A) (R : type676 A B) : term40 A B P R.
Proof. exact (@lem3811289 (A -> Prop) B nat P R). Qed.
Lemma lem3811291 {A B : Type'} (f : type1411 A B) (b : B) : term41 A B f b.
Proof. exact (@lem3811290 A B (@FINITE A) (term42 A B f b)). Qed.
Lemma lem3811292 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term43 A B f b s) = (term44 A B f b s).
Proof. exact (eq_refl (term43 A B f b s)). Qed.
Lemma lem3811293 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3811294 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term45 A B f b s a) = (term46 A B f b s a).
Proof. exact (MK_COMB (@lem3811292 A B f b s) (@lem3811293 B a)). Qed.
Lemma lem3811295 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term46 A B f b s a) = (term47 A B f b s a).
Proof. exact (eq_refl (term46 A B f b s a)). Qed.
Lemma lem3811296 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term45 A B f b s a) = (term47 A B f b s a).
Proof. exact (TRANS (@lem3811294 A B f b s a) (@lem3811295 A B f b s a)). Qed.
Lemma lem3811297 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3811298 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term48 A B f b s a n) = (term49 A B f b s a n).
Proof. exact (MK_COMB (@lem3811296 A B f b s a) (@lem3811297 n)). Qed.
Lemma lem3811299 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term49 A B f b s a n) = (@FINREC A B f b s a n).
Proof. exact (eq_refl (term49 A B f b s a n)). Qed.
Lemma lem3811300 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term48 A B f b s a n) = (@FINREC A B f b s a n).
Proof. exact (TRANS (@lem3811298 A B f b s a n) (@lem3811299 A B f b s a n)). Qed.
Lemma lem3811301 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term50 A B f b s a) = (term47 A B f b s a).
Proof. exact (fun_ext (fun n : nat => @lem3811300 A B f b s a n)). Qed.
Lemma lem3811302 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3811303 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term51 A B f b s a) = (term52 A B f b s a).
Proof. exact (MK_COMB (@lem3811302) (@lem3811301 A B f b s a)). Qed.
Lemma lem3811304 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term53 A B f b s) = (term54 A B f b s).
Proof. exact (fun_ext (fun a : B => @lem3811303 A B f b s a)). Qed.
Lemma lem3811305 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3811306 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term55 A B f b s) = (term56 A B f b s).
Proof. exact (MK_COMB (@lem3811305 B) (@lem3811304 A B f b s)). Qed.
Lemma lem3811307 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem3811308 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term58 A B f b s) = (term59 A B f b s).
Proof. exact (MK_COMB (@lem3811307 A s) (@lem3811306 A B f b s)). Qed.
Lemma lem3811309 {A B : Type'} (f : type1411 A B) (b : B) : (term60 A B f b) = (term61 A B f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3811308 A B f b s)). Qed.
Lemma lem3811310 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3811311 {A B : Type'} (f : type1411 A B) (b : B) : (term62 A B f b) = (term25 A B f b).
Proof. exact (MK_COMB (@lem3811310 A) (@lem3811309 A B f b)). Qed.
Lemma lem3811312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3811313 {A B : Type'} (f : type1411 A B) (b : B) : (term63 A B f b) = (term64 A B f b).
Proof. exact (MK_COMB (@lem3811312) (@lem3811311 A B f b)). Qed.
Lemma lem3811314 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term43 A B f b s) = (term44 A B f b s).
Proof. exact (eq_refl (term43 A B f b s)). Qed.
Lemma lem3811315 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem3811316 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) : (term45 A B f b s a1) = (term46 A B f b s a1).
Proof. exact (MK_COMB (@lem3811314 A B f b s) (@lem3811315 B a1)). Qed.
Lemma lem3811317 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) : (term46 A B f b s a1) = (term47 A B f b s a1).
Proof. exact (eq_refl (term46 A B f b s a1)). Qed.
Lemma lem3811318 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) : (term45 A B f b s a1) = (term47 A B f b s a1).
Proof. exact (TRANS (@lem3811316 A B f b s a1) (@lem3811317 A B f b s a1)). Qed.
Lemma lem3811319 (n1 : nat) : n1 = n1.
Proof. exact (eq_refl n1). Qed.
Lemma lem3811320 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) : (term48 A B f b s a1 n1) = (term49 A B f b s a1 n1).
Proof. exact (MK_COMB (@lem3811318 A B f b s a1) (@lem3811319 n1)). Qed.
Lemma lem3811321 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) : (term49 A B f b s a1 n1) = (@FINREC A B f b s a1 n1).
Proof. exact (eq_refl (term49 A B f b s a1 n1)). Qed.
Lemma lem3811322 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) : (term48 A B f b s a1 n1) = (@FINREC A B f b s a1 n1).
Proof. exact (TRANS (@lem3811320 A B f b s a1 n1) (@lem3811321 A B f b s a1 n1)). Qed.
Lemma lem3811323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3811324 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) : (term65 A B f b s a1 n1) = (term66 A B f b s a1 n1).
Proof. exact (MK_COMB (@lem3811323) (@lem3811322 A B f b s a1 n1)). Qed.
Lemma lem3811325 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term43 A B f b s) = (term44 A B f b s).
Proof. exact (eq_refl (term43 A B f b s)). Qed.
Lemma lem3811326 {B : Type'} (a2 : B) : a2 = a2.
Proof. exact (eq_refl a2). Qed.
Lemma lem3811327 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) : (term45 A B f b s a2) = (term46 A B f b s a2).
Proof. exact (MK_COMB (@lem3811325 A B f b s) (@lem3811326 B a2)). Qed.
Lemma lem3811328 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) : (term46 A B f b s a2) = (term47 A B f b s a2).
Proof. exact (eq_refl (term46 A B f b s a2)). Qed.
Lemma lem3811329 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) : (term45 A B f b s a2) = (term47 A B f b s a2).
Proof. exact (TRANS (@lem3811327 A B f b s a2) (@lem3811328 A B f b s a2)). Qed.
Lemma lem3811330 (n2 : nat) : n2 = n2.
Proof. exact (eq_refl n2). Qed.
Lemma lem3811331 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term48 A B f b s a2 n2) = (term49 A B f b s a2 n2).
Proof. exact (MK_COMB (@lem3811329 A B f b s a2) (@lem3811330 n2)). Qed.
Lemma lem3811332 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term49 A B f b s a2 n2) = (@FINREC A B f b s a2 n2).
Proof. exact (eq_refl (term49 A B f b s a2 n2)). Qed.
Lemma lem3811333 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term48 A B f b s a2 n2) = (@FINREC A B f b s a2 n2).
Proof. exact (TRANS (@lem3811331 A B f b s a2 n2) (@lem3811332 A B f b s a2 n2)). Qed.
Lemma lem3811334 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term67 A B a1 n1 f b s a2 n2) = (term68 A B a1 n1 f b s a2 n2).
Proof. exact (MK_COMB (@lem3811324 A B f b s a1 n1) (@lem3811333 A B f b s a2 n2)). Qed.
Lemma lem3811335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811336 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term69 A B a1 n1 f b s a2 n2) = (term70 A B a1 n1 f b s a2 n2).
Proof. exact (MK_COMB (@lem3811335) (@lem3811334 A B a1 n1 f b s a2 n2)). Qed.
Lemma lem3811337 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term71 B a1 a2 n1 n2) = (term71 B a1 a2 n1 n2).
Proof. exact (eq_refl (term71 B a1 a2 n1 n2)). Qed.
Lemma lem3811338 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term72 A B f b s a1 a2 n1 n2) = (term73 A B f b s a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3811336 A B a1 n1 f b s a2 n2) (@lem3811337 B a1 a2 n1 n2)). Qed.
Lemma lem3811339 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term74 A B f b s a1 n1 n2) = (term75 A B f b s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3811338 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3811340 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3811341 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term76 A B f b s a1 n1 n2) = (term77 A B f b s a1 n1 n2).
Proof. exact (MK_COMB (@lem3811340 B) (@lem3811339 A B f b s a1 n1 n2)). Qed.
Lemma lem3811342 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term78 A B f b s n1 n2) = (term79 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3811341 A B f b s a1 n1 n2)). Qed.
Lemma lem3811343 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3811344 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term80 A B f b s n1 n2) = (term81 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3811343 B) (@lem3811342 A B f b s n1 n2)). Qed.
Lemma lem3811345 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term82 A B f b n1 n2) = (term83 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3811344 A B f b s n1 n2)). Qed.
Lemma lem3811346 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3811347 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term84 A B f b n1 n2) = (term85 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3811346 A) (@lem3811345 A B f b n1 n2)). Qed.
Lemma lem3811348 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term86 A B f b n1) = (term87 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3811347 A B f b n1 n2)). Qed.
Lemma lem3811349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3811350 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term88 A B f b n1) = (term89 A B f b n1).
Proof. exact (MK_COMB (@lem3811349) (@lem3811348 A B f b n1)). Qed.
Lemma lem3811351 {A B : Type'} (f : type1411 A B) (b : B) : (term90 A B f b) = (term91 A B f b).
Proof. exact (fun_ext (fun n1 : nat => @lem3811350 A B f b n1)). Qed.
Lemma lem3811352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3811353 {A B : Type'} (f : type1411 A B) (b : B) : (term92 A B f b) = (term32 A B f b).
Proof. exact (MK_COMB (@lem3811352) (@lem3811351 A B f b)). Qed.
Lemma lem3811354 {A B : Type'} (f : type1411 A B) (b : B) : (term93 A B f b) = (term39 A B f b).
Proof. exact (MK_COMB (@lem3811313 A B f b) (@lem3811353 A B f b)). Qed.
Lemma lem3811355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811356 {A B : Type'} (f : type1411 A B) (b : B) : (term94 A B f b) = (term95 A B f b).
Proof. exact (MK_COMB (@lem3811355) (@lem3811354 A B f b)). Qed.
Lemma lem3811357 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term43 A B f b s) = (term44 A B f b s).
Proof. exact (eq_refl (term43 A B f b s)). Qed.
Lemma lem3811358 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3811359 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term45 A B f b s a) = (term46 A B f b s a).
Proof. exact (MK_COMB (@lem3811357 A B f b s) (@lem3811358 B a)). Qed.
Lemma lem3811360 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term46 A B f b s a) = (term47 A B f b s a).
Proof. exact (eq_refl (term46 A B f b s a)). Qed.
Lemma lem3811361 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term45 A B f b s a) = (term47 A B f b s a).
Proof. exact (TRANS (@lem3811359 A B f b s a) (@lem3811360 A B f b s a)). Qed.
Lemma lem3811362 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3811363 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term48 A B f b s a n) = (term49 A B f b s a n).
Proof. exact (MK_COMB (@lem3811361 A B f b s a) (@lem3811362 n)). Qed.
Lemma lem3811364 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term49 A B f b s a n) = (@FINREC A B f b s a n).
Proof. exact (eq_refl (term49 A B f b s a n)). Qed.
Lemma lem3811365 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term48 A B f b s a n) = (@FINREC A B f b s a n).
Proof. exact (TRANS (@lem3811363 A B f b s a n) (@lem3811364 A B f b s a n)). Qed.
Lemma lem3811366 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term50 A B f b s a) = (term47 A B f b s a).
Proof. exact (fun_ext (fun n : nat => @lem3811365 A B f b s a n)). Qed.
Lemma lem3811367 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3811368 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term51 A B f b s a) = (term52 A B f b s a).
Proof. exact (MK_COMB (@lem3811367) (@lem3811366 A B f b s a)). Qed.
Lemma lem3811369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3811370 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term96 A B f b s a) = (term97 A B f b s a).
Proof. exact (MK_COMB (@lem3811369) (@lem3811368 A B f b s a)). Qed.
Lemma lem3811371 {A B : Type'} (f : type685 A B) (s : A -> Prop) (a : B) : ((f s) = a) = ((f s) = a).
Proof. exact (eq_refl ((f s) = a)). Qed.
Lemma lem3811372 {A B : Type'} (f : type1411 A B) (b : B) (f' : type685 A B) (s : A -> Prop) (a : B) : ((term51 A B f b s a) = ((f' s) = a)) = ((term52 A B f b s a) = ((f' s) = a)).
Proof. exact (MK_COMB (@lem3811370 A B f b s a) (@lem3811371 A B f' s a)). Qed.
Lemma lem3811373 {A : Type'} (s : A -> Prop) : (term57 A s) = (term57 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem3811374 {A B : Type'} (f : type1411 A B) (b : B) (f' : type685 A B) (s : A -> Prop) (a : B) : (term98 A B f b f' s a) = (term99 A B f b f' s a).
Proof. exact (MK_COMB (@lem3811373 A s) (@lem3811372 A B f b f' s a)). Qed.
Lemma lem3811375 {A B : Type'} (f : type1411 A B) (b : B) (f' : type685 A B) (s : A -> Prop) : (term100 A B f b f' s) = (term101 A B f b f' s).
Proof. exact (fun_ext (fun a : B => @lem3811374 A B f b f' s a)). Qed.
Lemma lem3811376 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3811377 {A B : Type'} (f : type1411 A B) (b : B) (f' : type685 A B) (s : A -> Prop) : (term102 A B f b f' s) = (term103 A B f b f' s).
Proof. exact (MK_COMB (@lem3811376 B) (@lem3811375 A B f b f' s)). Qed.
Lemma lem3811378 {A B : Type'} (f : type1411 A B) (b : B) (f' : type685 A B) : (term104 A B f b f') = (term105 A B f b f').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3811377 A B f b f' s)). Qed.
Lemma lem3811379 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3811380 {A B : Type'} (f : type1411 A B) (b : B) (f' : type685 A B) : (term106 A B f b f') = (term107 A B f b f').
Proof. exact (MK_COMB (@lem3811379 A) (@lem3811378 A B f b f')). Qed.
Lemma lem3811381 {A B : Type'} (f : type1411 A B) (b : B) : (term108 A B f b) = (term109 A B f b).
Proof. exact (fun_ext (fun f' : type685 A B => @lem3811380 A B f b f')). Qed.
Lemma lem3811382 {A B : Type'} : (@ex ((A -> Prop) -> B)) = (@ex ((A -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> B))). Qed.
Lemma lem3811383 {A B : Type'} (f : type1411 A B) (b : B) : (term110 A B f b) = (term111 A B f b).
Proof. exact (MK_COMB (@lem3811382 A B) (@lem3811381 A B f b)). Qed.
Lemma lem3811384 {A B : Type'} (f : type1411 A B) (b : B) : (term41 A B f b) = (term112 A B f b).
Proof. exact (MK_COMB (@lem3811356 A B f b) (@lem3811383 A B f b)). Qed.
Lemma lem3811385 {A B : Type'} (f : type1411 A B) (b : B) : term112 A B f b.
Proof. exact (EQ_MP (@lem3811384 A B f b) (@lem3811291 A B f b)). Qed.
Lemma lem3811386 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term39 A B f b) : term111 A B f b.
Proof. exact (@lem3811385 A B f b (@lem3811287 A B f b h1)). Qed.
Lemma lem3811387 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term111 A B f b) : term111 A B f b.
Proof. exact (h1). Qed.
Lemma lem3811388 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term107 A B f b g.
Proof. exact (h1). Qed.
Lemma lem3811389 {A : Type'} (h1 : @FINITE A (@EMPTY A)) : @FINITE A (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3811416 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term107 A B f b g.
Proof. exact (h1). Qed.
Lemma lem3811417 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term113 A B f b g s.
Proof. exact (@lem3811416 A B f b g h1 s). Qed.
Lemma lem3811418 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term113 A B f b g s) = (term103 A B f b g s).
Proof. exact (eq_refl (term113 A B f b g s)). Qed.
Lemma lem3811419 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term103 A B f b g s.
Proof. exact (EQ_MP (@lem3811418 A B f b g s) (@lem3811417 A B s f b g h1)). Qed.
Lemma lem3811420 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term114 A B f b g s a.
Proof. exact (@lem3811419 A B s f b g h1 a). Qed.
Lemma lem3811421 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (a : B) : (term114 A B f b g s a) = (term99 A B f b g s a).
Proof. exact (eq_refl (term114 A B f b g s a)). Qed.
Lemma lem3811422 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term99 A B f b g s a.
Proof. exact (EQ_MP (@lem3811421 A B f b g s a) (@lem3811420 A B s a f b g h1)). Qed.
Lemma lem3811423 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3811424 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : (term52 A B f b s a) = ((g s) = a).
Proof. exact (@lem3811422 A B s a f b g h1 (@lem3811423 A s h2)). Qed.
Lemma lem3811425 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : term115 A B f b g s.
Proof. exact (fun a : B => @lem3811424 A B a f b g s h1 h2). Qed.
Lemma lem3811426 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (fun h0 : @FINITE A s => @lem3811425 A B f b g s h1 h0). Qed.
Lemma lem3811427 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term117 A B f b g.
Proof. exact (fun s : A -> Prop => @lem3811426 A B s f b g h1). Qed.
Lemma lem3811428 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) : term118 A B f b g.
Proof. exact (fun h0 : term107 A B f b g => @lem3811427 A B f b g h0). Qed.
Lemma lem3811429 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term117 A B f b g.
Proof. exact (@lem3811428 A B f b g (@lem3811388 A B f b g h1)). Qed.
Lemma lem3811430 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term119 A B f b g s.
Proof. exact (@lem3811429 A B f b g h1 s). Qed.
Lemma lem3811431 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term119 A B f b g s) = (term116 A B f b g s).
Proof. exact (eq_refl (term119 A B f b g s)). Qed.
Lemma lem3811434 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (EQ_MP (@lem3811431 A B f b g s) (@lem3811430 A B s f b g h1)). Qed.
Lemma lem3811435 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (@lem3811434 A B s f b g h1). Qed.
Lemma lem3811436 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term120 A B f b g.
Proof. exact (@lem3811435 A B (@EMPTY A) f b g h1). Qed.
Lemma lem3811437 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : term121 A B f b g.
Proof. exact (@lem3811436 A B f b g h1 (@lem3811389 A h2)). Qed.
Lemma lem3811439 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (a : B) (h1 : (term122 A B f b a) = ((g (@EMPTY A)) = a)) : (term122 A B f b a) = ((g (@EMPTY A)) = a).
Proof. exact (h1). Qed.
Lemma lem3811440 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (a : B) (h1 : (term122 A B f b a) = ((g (@EMPTY A)) = a)) : ((g (@EMPTY A)) = a) = (term122 A B f b a).
Proof. exact (SYM (@lem3811439 A B f b g a h1)). Qed.
Lemma lem3811441 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (a : B) (h1 : ((g (@EMPTY A)) = a) = (term122 A B f b a)) : ((g (@EMPTY A)) = a) = (term122 A B f b a).
Proof. exact (h1). Qed.
Lemma lem3811442 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (a : B) (h1 : ((g (@EMPTY A)) = a) = (term122 A B f b a)) : (term122 A B f b a) = ((g (@EMPTY A)) = a).
Proof. exact (SYM (@lem3811441 A B g f b a h1)). Qed.
Lemma lem3811443 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (a : B) : ((term122 A B f b a) = ((g (@EMPTY A)) = a)) = (((g (@EMPTY A)) = a) = (term122 A B f b a)).
Proof. exact (prop_ext (fun h1 : (term122 A B f b a) = ((g (@EMPTY A)) = a) => @lem3811440 A B f b g a h1) (fun h1 : ((g (@EMPTY A)) = a) = (term122 A B f b a) => @lem3811442 A B g f b a h1)). Qed.
Lemma lem3811444 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) : (term123 A B f b g) = (term124 A B g f b).
Proof. exact (fun_ext (fun a : B => @lem3811443 A B g f b a)). Qed.
Lemma lem3811445 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3811446 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) : (term121 A B f b g) = (term125 A B g f b).
Proof. exact (MK_COMB (@lem3811445 B) (@lem3811444 A B g f b)). Qed.
Lemma lem3811447 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : term125 A B g f b.
Proof. exact (EQ_MP (@lem3811446 A B g f b) (@lem3811437 A B f b g h1 h2)). Qed.
Lemma lem3811448 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : term126 A B g f b a.
Proof. exact (@lem3811447 A B f b g h1 h2 a). Qed.
Lemma lem3811449 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (a : B) : (term126 A B g f b a) = (((g (@EMPTY A)) = a) = (term122 A B f b a)).
Proof. exact (eq_refl (term126 A B g f b a)). Qed.
Lemma lem3811452 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : ((g (@EMPTY A)) = a) = (term122 A B f b a).
Proof. exact (EQ_MP (@lem3811449 A B g f b a) (@lem3811448 A B a f b g h1 h2)). Qed.
Lemma lem3811453 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : ((g (@EMPTY A)) = a) = (term122 A B f b a).
Proof. exact (@lem3811452 A B a f b g h1 h2). Qed.
Lemma lem3811454 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : ((g (@EMPTY A)) = b) = (term127 A B f b).
Proof. exact (@lem3811453 A B b f b g h1 h2). Qed.
Lemma lem3811455 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : (term127 A B f b) = ((g (@EMPTY A)) = b).
Proof. exact (SYM (@lem3811454 A B f b g h1 h2)). Qed.
Lemma lem3811457 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3811245 A) (@lem3811244 A)). Qed.
Lemma lem3811458 {A : Type'} : True = (@FINITE A (@EMPTY A)).
Proof. exact (SYM (@lem3811457 A)). Qed.
Lemma lem3811459 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem3811458 A) (@lem0)). Qed.
Lemma lem3811461 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term128 A B f b s a) = (term129 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3811462 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term128 A B f b s a) = (term129 A B s a b).
Proof. exact (@lem3811461 A B f s a b). Qed.
Lemma lem3811463 {A B : Type'} (f : type1411 A B) (b : B) : (term130 A B f b) = (term131 A B b).
Proof. exact (@lem3811462 A B f (@EMPTY A) b b). Qed.
Lemma lem3811467 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3811468 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3811467 (A -> Prop) x). Qed.
Lemma lem3811469 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3811468 A (@EMPTY A)). Qed.
Lemma lem3811470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3811471 {A : Type'} : (term132 A) = (and True).
Proof. exact (MK_COMB (@lem3811470) (@lem3811469 A)). Qed.
Lemma lem3811473 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3811474 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3811473 B x). Qed.
Lemma lem3811475 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem3811474 B b). Qed.
Lemma lem3811476 {A B : Type'} (b : B) : (term131 A B b) = (True /\ True).
Proof. exact (MK_COMB (@lem3811471 A) (@lem3811475 B b)). Qed.
Lemma lem3811478 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3811479 : (True /\ True) = True.
Proof. exact (@lem3811478 True). Qed.
Lemma lem3811480 {A B : Type'} (b : B) : (term131 A B b) = True.
Proof. exact (TRANS (@lem3811476 A B b) (@lem3811479)). Qed.
Lemma lem3811481 {A B : Type'} (f : type1411 A B) (b : B) : (term130 A B f b) = True.
Proof. exact (TRANS (@lem3811463 A B f b) (@lem3811480 A B b)). Qed.
Lemma lem3811482 {A B : Type'} (f : type1411 A B) (b : B) : True = (term130 A B f b).
Proof. exact (SYM (@lem3811481 A B f b)). Qed.
Lemma lem3811483 {A B : Type'} (f : type1411 A B) (b : B) : term130 A B f b.
Proof. exact (EQ_MP (@lem3811482 A B f b) (@lem0)). Qed.
Lemma lem3811484 {A B : Type'} (f : type1411 A B) (b : B) : term127 A B f b.
Proof. exact (ex_intro (term133 A B f b) (NUMERAL 0) (@lem3811483 A B f b)). Qed.
Lemma lem3811485 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) (h2 : @FINITE A (@EMPTY A)) : (g (@EMPTY A)) = b.
Proof. exact (EQ_MP (@lem3811455 A B f b g h1 h2) (@lem3811484 A B f b)). Qed.
Lemma lem3811486 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : (@FINITE A (@EMPTY A)) = ((g (@EMPTY A)) = b).
Proof. exact (prop_ext (fun h2 : @FINITE A (@EMPTY A) => @lem3811485 A B f b g h1 h2) (fun h2 : (g (@EMPTY A)) = b => @lem3811459 A)). Qed.
Lemma lem3811487 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : (g (@EMPTY A)) = b.
Proof. exact (EQ_MP (@lem3811486 A B f b g h1) (@lem3811459 A)). Qed.
Lemma lem3811488 {A : Type'} (x : A) (s : A -> Prop) (h1 : term134 A x s) : term134 A x s.
Proof. exact (h1). Qed.
Lemma lem3811489 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3811490 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3811517 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term107 A B f b g.
Proof. exact (h1). Qed.
Lemma lem3811518 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term113 A B f b g s.
Proof. exact (@lem3811517 A B f b g h1 s). Qed.
Lemma lem3811519 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term113 A B f b g s) = (term103 A B f b g s).
Proof. exact (eq_refl (term113 A B f b g s)). Qed.
Lemma lem3811520 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term103 A B f b g s.
Proof. exact (EQ_MP (@lem3811519 A B f b g s) (@lem3811518 A B s f b g h1)). Qed.
Lemma lem3811521 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term114 A B f b g s a.
Proof. exact (@lem3811520 A B s f b g h1 a). Qed.
Lemma lem3811522 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (a : B) : (term114 A B f b g s a) = (term99 A B f b g s a).
Proof. exact (eq_refl (term114 A B f b g s a)). Qed.
Lemma lem3811523 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term99 A B f b g s a.
Proof. exact (EQ_MP (@lem3811522 A B f b g s a) (@lem3811521 A B s a f b g h1)). Qed.
Lemma lem3811524 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3811525 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : (term52 A B f b s a) = ((g s) = a).
Proof. exact (@lem3811523 A B s a f b g h1 (@lem3811524 A s h2)). Qed.
Lemma lem3811526 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : term115 A B f b g s.
Proof. exact (fun a : B => @lem3811525 A B a f b g s h1 h2). Qed.
Lemma lem3811527 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (fun h0 : @FINITE A s => @lem3811526 A B f b g s h1 h0). Qed.
Lemma lem3811528 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term117 A B f b g.
Proof. exact (fun s : A -> Prop => @lem3811527 A B s f b g h1). Qed.
Lemma lem3811529 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) : term118 A B f b g.
Proof. exact (fun h0 : term107 A B f b g => @lem3811528 A B f b g h0). Qed.
Lemma lem3811530 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term117 A B f b g.
Proof. exact (@lem3811529 A B f b g (@lem3811388 A B f b g h1)). Qed.
Lemma lem3811531 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term119 A B f b g s.
Proof. exact (@lem3811530 A B f b g h1 s). Qed.
Lemma lem3811532 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term119 A B f b g s) = (term116 A B f b g s).
Proof. exact (eq_refl (term119 A B f b g s)). Qed.
Lemma lem3811535 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (EQ_MP (@lem3811532 A B f b g s) (@lem3811531 A B s f b g h1)). Qed.
Lemma lem3811536 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (@lem3811535 A B s f b g h1). Qed.
Lemma lem3811537 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : term115 A B f b g s.
Proof. exact (@lem3811536 A B s f b g h1 (@lem3811232 A s h2)). Qed.
Lemma lem3811538 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : term115 A B f b g s.
Proof. exact (h1). Qed.
Lemma lem3811540 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (a : B) (h1 : (term52 A B f b s a) = ((g s) = a)) : (term52 A B f b s a) = ((g s) = a).
Proof. exact (h1). Qed.
Lemma lem3811541 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (a : B) (h1 : (term52 A B f b s a) = ((g s) = a)) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (SYM (@lem3811540 A B f b g s a h1)). Qed.
Lemma lem3811542 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (h1 : ((g s) = a) = (term52 A B f b s a)) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (h1). Qed.
Lemma lem3811543 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (h1 : ((g s) = a) = (term52 A B f b s a)) : (term52 A B f b s a) = ((g s) = a).
Proof. exact (SYM (@lem3811542 A B g f b s a h1)). Qed.
Lemma lem3811544 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : ((term52 A B f b s a) = ((g s) = a)) = (((g s) = a) = (term52 A B f b s a)).
Proof. exact (prop_ext (fun h1 : (term52 A B f b s a) = ((g s) = a) => @lem3811541 A B f b g s a h1) (fun h1 : ((g s) = a) = (term52 A B f b s a) => @lem3811543 A B g f b s a h1)). Qed.
Lemma lem3811545 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term135 A B f b g s) = (term136 A B g f b s).
Proof. exact (fun_ext (fun a : B => @lem3811544 A B g f b s a)). Qed.
Lemma lem3811546 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3811547 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term115 A B f b g s) = (term137 A B g f b s).
Proof. exact (MK_COMB (@lem3811546 B) (@lem3811545 A B g f b s)). Qed.
Lemma lem3811548 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : term137 A B g f b s.
Proof. exact (EQ_MP (@lem3811547 A B g f b s) (@lem3811538 A B f b g s h1)). Qed.
Lemma lem3811572 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : term138 A B g f b s a.
Proof. exact (@lem3811548 A B f b g s h1 a). Qed.
Lemma lem3811573 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term138 A B g f b s a) = (((g s) = a) = (term52 A B f b s a)).
Proof. exact (eq_refl (term138 A B g f b s a)). Qed.
Lemma lem3811576 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (EQ_MP (@lem3811573 A B g f b s a) (@lem3811572 A B a f b g s h1)). Qed.
Lemma lem3811577 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (@lem3811576 A B a f b g s h1). Qed.
Lemma lem3811578 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = (term139 A B f g s x)) = (term140 A B b f g s x).
Proof. exact (@lem3811577 A B (term139 A B f g s x) f b g s h1). Qed.
Lemma lem3811583 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term140 A B b f g s x) = ((g s) = (term139 A B f g s x)).
Proof. exact (SYM (@lem3811578 A B x f b g s h1)). Qed.
Lemma lem3811584 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : term141 A B f b g s.
Proof. exact (@lem3811548 A B f b g s h1 (g s)). Qed.
Lemma lem3811585 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term141 A B f b g s) = (((g s) = (g s)) = (term142 A B f b g s)).
Proof. exact (eq_refl (term141 A B f b g s)). Qed.
Lemma lem3811586 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = (g s)) = (term142 A B f b g s).
Proof. exact (EQ_MP (@lem3811585 A B f b g s) (@lem3811584 A B f b g s h1)). Qed.
Lemma lem3811594 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3811595 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3811594 B x). Qed.
Lemma lem3811596 {A B : Type'} (g : type685 A B) (s : A -> Prop) : ((g s) = (g s)) = True.
Proof. exact (@lem3811595 B (g s)). Qed.
Lemma lem3811597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3811598 {A B : Type'} (g : type685 A B) (s : A -> Prop) : (term143 A B g s) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3811597) (@lem3811596 A B g s)). Qed.
Lemma lem3811603 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term142 A B f b g s) = (term142 A B f b g s).
Proof. exact (eq_refl (term142 A B f b g s)). Qed.
Lemma lem3811604 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (((g s) = (g s)) = (term142 A B f b g s)) = (True = (term142 A B f b g s)).
Proof. exact (MK_COMB (@lem3811598 A B g s) (@lem3811603 A B f b g s)). Qed.
Lemma lem3811606 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3811607 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (True = (term142 A B f b g s)) = (term142 A B f b g s).
Proof. exact (@lem3811606 (term142 A B f b g s)). Qed.
Lemma lem3811612 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (((g s) = (g s)) = (term142 A B f b g s)) = (term142 A B f b g s).
Proof. exact (TRANS (@lem3811604 A B f b g s) (@lem3811607 A B f b g s)). Qed.
Lemma lem3811613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811614 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term144 A B f b g s) = (term145 A B f b g s).
Proof. exact (MK_COMB (@lem3811613) (@lem3811612 A B f b g s)). Qed.
Lemma lem3811619 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term140 A B b f g s x) = (term140 A B b f g s x).
Proof. exact (eq_refl (term140 A B b f g s x)). Qed.
Lemma lem3811620 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term146 A B b f g s x) = (term147 A B b f g s x).
Proof. exact (MK_COMB (@lem3811614 A B f b g s) (@lem3811619 A B b f g s x)). Qed.
Lemma lem3811623 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term147 A B b f g s x) = (term146 A B b f g s x).
Proof. exact (SYM (@lem3811620 A B b f g s x)). Qed.
Lemma lem3811625 {A : Type'} (P : A -> Prop) (Q : Prop) : (term16 A P Q) = (term17 A P Q).
Proof. exact (EQ_MP (@lem3811230 A P Q) (@lem3811229 A P Q)). Qed.
Lemma lem3811626 (P : nat -> Prop) (Q : Prop) : (term148 P Q) = (term149 P Q).
Proof. exact (@lem3811625 nat P Q). Qed.
Lemma lem3811627 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term150 A B b f g s x) = (term151 A B b f g s x).
Proof. exact (@lem3811626 (term152 A B f b g s) (term140 A B b f g s x)). Qed.
Lemma lem3811628 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) : (term153 A B f b g s n) = (term154 A B f b g s n).
Proof. exact (eq_refl (term153 A B f b g s n)). Qed.
Lemma lem3811629 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term155 A B f b g s) = (term152 A B f b g s).
Proof. exact (fun_ext (fun n : nat => @lem3811628 A B f b g s n)). Qed.
Lemma lem3811630 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3811631 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term156 A B f b g s) = (term142 A B f b g s).
Proof. exact (MK_COMB (@lem3811630) (@lem3811629 A B f b g s)). Qed.
Lemma lem3811632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811633 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term157 A B f b g s) = (term145 A B f b g s).
Proof. exact (MK_COMB (@lem3811632) (@lem3811631 A B f b g s)). Qed.
Lemma lem3811634 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term140 A B b f g s x) = (term140 A B b f g s x).
Proof. exact (eq_refl (term140 A B b f g s x)). Qed.
Lemma lem3811635 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term150 A B b f g s x) = (term147 A B b f g s x).
Proof. exact (MK_COMB (@lem3811633 A B f b g s) (@lem3811634 A B b f g s x)). Qed.
Lemma lem3811636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3811637 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term158 A B b f g s x) = (term159 A B b f g s x).
Proof. exact (MK_COMB (@lem3811636) (@lem3811635 A B b f g s x)). Qed.
Lemma lem3811638 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) : (term153 A B f b g s n) = (term154 A B f b g s n).
Proof. exact (eq_refl (term153 A B f b g s n)). Qed.
Lemma lem3811639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811640 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) : (term160 A B f b g s n) = (term161 A B f b g s n).
Proof. exact (MK_COMB (@lem3811639) (@lem3811638 A B f b g s n)). Qed.
Lemma lem3811641 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term140 A B b f g s x) = (term140 A B b f g s x).
Proof. exact (eq_refl (term140 A B b f g s x)). Qed.
Lemma lem3811642 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term162 A B n b f g s x) = (term163 A B n b f g s x).
Proof. exact (MK_COMB (@lem3811640 A B f b g s n) (@lem3811641 A B b f g s x)). Qed.
Lemma lem3811643 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term164 A B b f g s x) = (term165 A B b f g s x).
Proof. exact (fun_ext (fun n : nat => @lem3811642 A B n b f g s x)). Qed.
Lemma lem3811644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3811645 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term151 A B b f g s x) = (term166 A B b f g s x).
Proof. exact (MK_COMB (@lem3811644) (@lem3811643 A B b f g s x)). Qed.
Lemma lem3811646 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : ((term150 A B b f g s x) = (term151 A B b f g s x)) = ((term147 A B b f g s x) = (term166 A B b f g s x)).
Proof. exact (MK_COMB (@lem3811637 A B b f g s x) (@lem3811645 A B b f g s x)). Qed.
Lemma lem3811647 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term147 A B b f g s x) = (term166 A B b f g s x).
Proof. exact (EQ_MP (@lem3811646 A B b f g s x) (@lem3811627 A B b f g s x)). Qed.
Lemma lem3811658 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term166 A B b f g s x) = (term147 A B b f g s x).
Proof. exact (SYM (@lem3811647 A B b f g s x)). Qed.
Lemma lem3811660 (P : nat -> Prop) : term167 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem3811661 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : term168 A B b f g s x.
Proof. exact (@lem3811660 (term165 A B b f g s x)). Qed.
Lemma lem3811662 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term169 A B b f g s x) = (term170 A B b f g s x).
Proof. exact (eq_refl (term169 A B b f g s x)). Qed.
Lemma lem3811663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3811664 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term171 A B b f g s x) = (term172 A B b f g s x).
Proof. exact (MK_COMB (@lem3811663) (@lem3811662 A B b f g s x)). Qed.
Lemma lem3811665 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term173 A B b f g s x n) = (term163 A B n b f g s x).
Proof. exact (eq_refl (term173 A B b f g s x n)). Qed.
Lemma lem3811666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811667 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term174 A B b f g s x n) = (term175 A B n b f g s x).
Proof. exact (MK_COMB (@lem3811666) (@lem3811665 A B n b f g s x)). Qed.
Lemma lem3811668 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term176 A B b f g s x n) = (term177 A B n b f g s x).
Proof. exact (eq_refl (term176 A B b f g s x n)). Qed.
Lemma lem3811669 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term178 A B b f g s x n) = (term179 A B n b f g s x).
Proof. exact (MK_COMB (@lem3811667 A B n b f g s x) (@lem3811668 A B n b f g s x)). Qed.
Lemma lem3811670 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term180 A B b f g s x) = (term181 A B b f g s x).
Proof. exact (fun_ext (fun n : nat => @lem3811669 A B n b f g s x)). Qed.
Lemma lem3811671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3811672 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term182 A B b f g s x) = (term183 A B b f g s x).
Proof. exact (MK_COMB (@lem3811671) (@lem3811670 A B b f g s x)). Qed.
Lemma lem3811673 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term184 A B b f g s x) = (term185 A B b f g s x).
Proof. exact (MK_COMB (@lem3811664 A B b f g s x) (@lem3811672 A B b f g s x)). Qed.
Lemma lem3811674 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811675 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term186 A B b f g s x) = (term187 A B b f g s x).
Proof. exact (MK_COMB (@lem3811674) (@lem3811673 A B b f g s x)). Qed.
Lemma lem3811676 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term173 A B b f g s x n) = (term163 A B n b f g s x).
Proof. exact (eq_refl (term173 A B b f g s x n)). Qed.
Lemma lem3811677 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term188 A B b f g s x) = (term165 A B b f g s x).
Proof. exact (fun_ext (fun n : nat => @lem3811676 A B n b f g s x)). Qed.
Lemma lem3811678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3811679 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term189 A B b f g s x) = (term166 A B b f g s x).
Proof. exact (MK_COMB (@lem3811678) (@lem3811677 A B b f g s x)). Qed.
Lemma lem3811680 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term168 A B b f g s x) = (term190 A B b f g s x).
Proof. exact (MK_COMB (@lem3811675 A B b f g s x) (@lem3811679 A B b f g s x)). Qed.
Lemma lem3811681 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : term190 A B b f g s x.
Proof. exact (EQ_MP (@lem3811680 A B b f g s x) (@lem3811661 A B b f g s x)). Qed.
Lemma lem3811708 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : term138 A B g f b s a.
Proof. exact (@lem3811548 A B f b g s h1 a). Qed.
Lemma lem3811709 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term138 A B g f b s a) = (((g s) = a) = (term52 A B f b s a)).
Proof. exact (eq_refl (term138 A B g f b s a)). Qed.
Lemma lem3811714 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term128 A B f b s a) = (term129 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3811715 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term128 A B f b s a) = (term129 A B s a b).
Proof. exact (@lem3811714 A B f s a b). Qed.
Lemma lem3811716 {A B : Type'} (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (b : B) : (term191 A B f b g s) = (term192 A B g s b).
Proof. exact (@lem3811715 A B f s (g s) b). Qed.
Lemma lem3811722 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (EQ_MP (@lem3811709 A B g f b s a) (@lem3811708 A B a f b g s h1)). Qed.
Lemma lem3811723 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (@lem3811722 A B a f b g s h1). Qed.
Lemma lem3811724 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = b) = (term193 A B f s b).
Proof. exact (@lem3811723 A B b f b g s h1). Qed.
Lemma lem3811729 {A : Type'} (s : A -> Prop) : (term194 A s) = (term194 A s).
Proof. exact (eq_refl (term194 A s)). Qed.
Lemma lem3811730 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term192 A B g s b) = (term195 A B f s b).
Proof. exact (MK_COMB (@lem3811729 A s) (@lem3811724 A B f b g s h1)). Qed.
Lemma lem3811733 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term191 A B f b g s) = (term195 A B f s b).
Proof. exact (TRANS (@lem3811716 A B f g s b) (@lem3811730 A B f b g s h1)). Qed.
Lemma lem3811734 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811735 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term196 A B f b g s) = (term197 A B f s b).
Proof. exact (MK_COMB (@lem3811734) (@lem3811733 A B f b g s h1)). Qed.
Lemma lem3811740 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term140 A B b f g s x) = (term140 A B b f g s x).
Proof. exact (eq_refl (term140 A B b f g s x)). Qed.
Lemma lem3811741 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term170 A B b f g s x) = (term198 A B b f g s x).
Proof. exact (MK_COMB (@lem3811735 A B f b g s h1) (@lem3811740 A B b f g s x)). Qed.
Lemma lem3811744 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term198 A B b f g s x) = (term170 A B b f g s x).
Proof. exact (SYM (@lem3811741 A B x f b g s h1)). Qed.
Lemma lem3811745 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : term195 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3811746 {A : Type'} (x : A) : term199 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3811747 {A : Type'} (x : A) : (term199 A x) = (term200 A x).
Proof. exact (eq_refl (term199 A x)). Qed.
Lemma lem3811748 {A : Type'} (x : A) : term200 A x.
Proof. exact (EQ_MP (@lem3811747 A x) (@lem3811746 A x)). Qed.
Lemma lem3811749 {A : Type'} (x : A) : term201 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3811782 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3811745 A B f s b h1)). Qed.
Lemma lem3811783 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3811784 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (@IN A x s) = (@IN A x (@EMPTY A)).
Proof. exact (MK_COMB (@lem3811783 A x) (@lem3811782 A B f s b h1)). Qed.
Lemma lem3811786 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3811749 A x (@lem3811748 A x)). Qed.
Lemma lem3811787 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3811786 A x). Qed.
Lemma lem3811788 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (@IN A x s) = False.
Proof. exact (TRANS (@lem3811784 A B x f s b h1) (@lem3811787 A x)). Qed.
Lemma lem3811789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3811790 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term202 A x s) = (imp False).
Proof. exact (MK_COMB (@lem3811789) (@lem3811788 A B x f s b h1)). Qed.
Lemma lem3811796 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3811745 A B f s b h1)). Qed.
Lemma lem3811797 {A B : Type'} (f : type1411 A B) (b : B) : (@FINREC A B f b) = (@FINREC A B f b).
Proof. exact (eq_refl (@FINREC A B f b)). Qed.
Lemma lem3811798 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (@FINREC A B f b s) = (@FINREC A B f b (@EMPTY A)).
Proof. exact (MK_COMB (@lem3811797 A B f b) (@lem3811796 A B f s b h1)). Qed.
Lemma lem3811800 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3811745 A B f s b h1)). Qed.
Lemma lem3811801 {A : Type'} : (@DELETE A) = (@DELETE A).
Proof. exact (eq_refl (@DELETE A)). Qed.
Lemma lem3811802 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (@DELETE A s) = (@DELETE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3811801 A) (@lem3811800 A B f s b h1)). Qed.
Lemma lem3811803 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3811804 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (@DELETE A s x) = (@DELETE A (@EMPTY A) x).
Proof. exact (MK_COMB (@lem3811802 A B f s b h1) (@lem3811803 A x)). Qed.
Lemma lem3811805 {A B : Type'} (g : type685 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3811806 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term203 A B g s x) = (term204 A B g x).
Proof. exact (MK_COMB (@lem3811805 A B g) (@lem3811804 A B x f s b h1)). Qed.
Lemma lem3811807 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3811808 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term139 A B f g s x) = (term205 A B f g x).
Proof. exact (MK_COMB (@lem3811807 A B f x) (@lem3811806 A B g x f s b h1)). Qed.
Lemma lem3811809 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term206 A B b f g s x) = (term207 A B b f g x).
Proof. exact (MK_COMB (@lem3811798 A B f s b h1) (@lem3811808 A B g x f s b h1)). Qed.
Lemma lem3811810 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3811811 {A B : Type'} (g : type685 A B) (x : A) (n : nat) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term208 A B b f g s x n) = (term209 A B b f g x n).
Proof. exact (MK_COMB (@lem3811809 A B g x f s b h1) (@lem3811810 n)). Qed.
Lemma lem3811812 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term210 A B b f g s x) = (term211 A B b f g x).
Proof. exact (fun_ext (fun n : nat => @lem3811811 A B g x n f s b h1)). Qed.
Lemma lem3811813 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3811814 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term140 A B b f g s x) = (term212 A B b f g x).
Proof. exact (MK_COMB (@lem3811813) (@lem3811812 A B g x f s b h1)). Qed.
Lemma lem3811819 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term213 A B b f g s x) = (term214 A B b f g x).
Proof. exact (MK_COMB (@lem3811790 A B x f s b h1) (@lem3811814 A B g x f s b h1)). Qed.
Lemma lem3811821 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3811822 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) : (term214 A B b f g x) = True.
Proof. exact (@lem3811821 (term212 A B b f g x)). Qed.
Lemma lem3811823 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : (term213 A B b f g s x) = True.
Proof. exact (TRANS (@lem3811819 A B g x f s b h1) (@lem3811822 A B b f g x)). Qed.
Lemma lem3811824 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : True = (term213 A B b f g s x).
Proof. exact (SYM (@lem3811823 A B g x f s b h1)). Qed.
Lemma lem3811825 {A B : Type'} (g : type685 A B) (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) (h1 : term195 A B f s b) : term213 A B b f g s x.
Proof. exact (EQ_MP (@lem3811824 A B g x f s b h1) (@lem0)). Qed.
Lemma lem3811826 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term195 A B f s b) (h2 : @IN A x s) : term140 A B b f g s x.
Proof. exact (@lem3811825 A B g x f s b h1 (@lem3811489 A x s h2)). Qed.
Lemma lem3811827 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term198 A B b f g s x.
Proof. exact (fun h0 : term195 A B f s b => @lem3811826 A B g f b x s h0 h1). Qed.
Lemma lem3811828 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : @IN A x s) : term170 A B b f g s x.
Proof. exact (EQ_MP (@lem3811744 A B x f b g s h1) (@lem3811827 A B b f g x s h2)). Qed.
Lemma lem3811829 {A B : Type'} (h1 : term215 A B) : term215 A B.
Proof. exact (h1). Qed.
Lemma lem3811830 {A B : Type'} (f : type1411 A B) (h1 : term215 A B) : term216 A B f.
Proof. exact (@lem3811829 A B h1 f). Qed.
Lemma lem3811831 {A B : Type'} (f : type1411 A B) : (term216 A B f) = (term217 A B f).
Proof. exact (eq_refl (term216 A B f)). Qed.
Lemma lem3811832 {A B : Type'} (f : type1411 A B) (h1 : term215 A B) : term217 A B f.
Proof. exact (EQ_MP (@lem3811831 A B f) (@lem3811830 A B f h1)). Qed.
Lemma lem3811833 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term215 A B) : term218 A B f b.
Proof. exact (@lem3811832 A B f h1 b). Qed.
Lemma lem3811834 {A B : Type'} (b : B) (f : type1411 A B) : (term218 A B f b) = (term219 A B b f).
Proof. exact (eq_refl (term218 A B f b)). Qed.
Lemma lem3811835 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term215 A B) : term219 A B b f.
Proof. exact (EQ_MP (@lem3811834 A B b f) (@lem3811833 A B f b h1)). Qed.
Lemma lem3811836 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term26 A B f.
Proof. exact (h1). Qed.
Lemma lem3811837 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) (h2 : term215 A B) : term220 A B b f.
Proof. exact (@lem3811835 A B b f h2 (@lem3811836 A B f h1)). Qed.
Lemma lem3811838 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) (h2 : term215 A B) : term221 A B f.
Proof. exact (fun b : B => @lem3811837 A B b f h1 h2). Qed.
Lemma lem3811839 {A B : Type'} (f : type1411 A B) (h1 : term215 A B) : term222 A B f.
Proof. exact (fun h0 : term26 A B f => @lem3811838 A B f h0 h1). Qed.
Lemma lem3811840 {A B : Type'} (h1 : term215 A B) : term223 A B.
Proof. exact (fun f : type1411 A B => @lem3811839 A B f h1). Qed.
Lemma lem3811841 {A B : Type'} : term224 A B.
Proof. exact (fun h0 : term215 A B => @lem3811840 A B h0). Qed.
Lemma lem3811842 {A B : Type'} : term223 A B.
Proof. exact (@lem3811841 A B (@lem3797397 A B)). Qed.
Lemma lem3811843 {A B : Type'} (f : type1411 A B) : term225 A B f.
Proof. exact (@lem3811842 A B f). Qed.
Lemma lem3811844 {A B : Type'} (f : type1411 A B) : (term225 A B f) = (term222 A B f).
Proof. exact (eq_refl (term225 A B f)). Qed.
Lemma lem3811847 {A B : Type'} (f : type1411 A B) : term222 A B f.
Proof. exact (EQ_MP (@lem3811844 A B f) (@lem3811843 A B f)). Qed.
Lemma lem3811848 {A B : Type'} (f : type1411 A B) : term222 A B f.
Proof. exact (@lem3811847 A B f). Qed.
Lemma lem3811849 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term221 A B f.
Proof. exact (@lem3811848 A B f (@lem3811259 A B f h1)). Qed.
Lemma lem3811945 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) (h1 : term226 A B f b g s n) : term226 A B f b g s n.
Proof. exact (h1). Qed.
Lemma lem3811993 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term227 A B f b.
Proof. exact (@lem3811849 A B f h1 b). Qed.
Lemma lem3811994 {A B : Type'} (b : B) (f : type1411 A B) : (term227 A B f b) = (term220 A B b f).
Proof. exact (eq_refl (term227 A B f b)). Qed.
Lemma lem3811995 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term220 A B b f.
Proof. exact (EQ_MP (@lem3811994 A B b f) (@lem3811993 A B b f h1)). Qed.
Lemma lem3811996 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term26 A B f) : term228 A B b f n.
Proof. exact (@lem3811995 A B b f h1 n). Qed.
Lemma lem3811997 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term228 A B b f n) = (term229 A B b n f).
Proof. exact (eq_refl (term228 A B b f n)). Qed.
Lemma lem3811998 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term26 A B f) : term229 A B b n f.
Proof. exact (EQ_MP (@lem3811997 A B b n f) (@lem3811996 A B b n f h1)). Qed.
Lemma lem3811999 {A B : Type'} (b : B) (n : nat) (s : A -> Prop) (f : type1411 A B) (h1 : term26 A B f) : term230 A B b n f s.
Proof. exact (@lem3811998 A B b n f h1 s). Qed.
Lemma lem3812000 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term230 A B b n f s) = (term231 A B b s n f).
Proof. exact (eq_refl (term230 A B b n f s)). Qed.
Lemma lem3812001 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (h1 : term26 A B f) : term231 A B b s n f.
Proof. exact (EQ_MP (@lem3812000 A B b s n f) (@lem3811999 A B b n s f h1)). Qed.
Lemma lem3812002 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term26 A B f) : term232 A B b s n f z.
Proof. exact (@lem3812001 A B b s n f h1 z). Qed.
Lemma lem3812003 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term232 A B b s n f z) = (term233 A B b s n z f).
Proof. exact (eq_refl (term232 A B b s n f z)). Qed.
Lemma lem3812006 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term26 A B f) : term233 A B b s n z f.
Proof. exact (EQ_MP (@lem3812003 A B b s n z f) (@lem3812002 A B b s n z f h1)). Qed.
Lemma lem3812007 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term26 A B f) : term233 A B b s n z f.
Proof. exact (@lem3812006 A B b s n z f h1). Qed.
Lemma lem3812008 {A B : Type'} (b : B) (n : nat) (g : type685 A B) (s : A -> Prop) (f : type1411 A B) (h1 : term26 A B f) : term234 A B b n g s f.
Proof. exact (@lem3812007 A B b s n (g s) f h1). Qed.
Lemma lem3812009 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) (h1 : term26 A B f) (h2 : term226 A B f b g s n) : term235 A B b n g s f.
Proof. exact (@lem3812008 A B b n g s f h1 (@lem3811945 A B f b g s n h2)). Qed.
Lemma lem3812010 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) (h1 : term26 A B f) (h2 : term226 A B f b g s n) : term236 A B b n g s f x.
Proof. exact (@lem3812009 A B f b g s n h1 h2 x). Qed.
Lemma lem3812011 {A B : Type'} (b : B) (n : nat) (g : type685 A B) (s : A -> Prop) (f : type1411 A B) (x : A) : (term236 A B b n g s f x) = (term237 A B b n g s f x).
Proof. exact (eq_refl (term236 A B b n g s f x)). Qed.
Lemma lem3812012 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) (h1 : term26 A B f) (h2 : term226 A B f b g s n) : term237 A B b n g s f x.
Proof. exact (EQ_MP (@lem3812011 A B b n g s f x) (@lem3812010 A B x f b g s n h1 h2)). Qed.
Lemma lem3812034 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem3812036 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : term138 A B g f b s a.
Proof. exact (@lem3811548 A B f b g s h1 a). Qed.
Lemma lem3812037 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term138 A B g f b s a) = (((g s) = a) = (term52 A B f b s a)).
Proof. exact (eq_refl (term138 A B g f b s a)). Qed.
Lemma lem3812060 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem3812034 A x s) (@lem3811489 A x s h1)). Qed.
Lemma lem3812061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3812062 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term202 A x s) = (imp True).
Proof. exact (MK_COMB (@lem3812061) (@lem3812060 A x s h1)). Qed.
Lemma lem3812070 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (EQ_MP (@lem3812037 A B g f b s a) (@lem3812036 A B a f b g s h1)). Qed.
Lemma lem3812071 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = a) = (term52 A B f b s a).
Proof. exact (@lem3812070 A B a f b g s h1). Qed.
Lemma lem3812072 {A B : Type'} (x : A) (w : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : ((g s) = (f x w)) = (term238 A B b s f x w).
Proof. exact (@lem3812071 A B (f x w) f b g s h1). Qed.
Lemma lem3812077 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) : (term239 A B f b s x w n) = (term239 A B f b s x w n).
Proof. exact (eq_refl (term239 A B f b s x w n)). Qed.
Lemma lem3812078 {A B : Type'} (n : nat) (x : A) (w : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term240 A B b n g s f x w) = (term241 A B n b s f x w).
Proof. exact (MK_COMB (@lem3812077 A B f b s x w n) (@lem3812072 A B x w f b g s h1)). Qed.
Lemma lem3812081 {A B : Type'} (n : nat) (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term242 A B b n g s f x) = (term243 A B n b s f x).
Proof. exact (fun_ext (fun w : B => @lem3812078 A B n x w f b g s h1)). Qed.
Lemma lem3812082 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3812083 {A B : Type'} (n : nat) (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term115 A B f b g s) : (term244 A B b n g s f x) = (term245 A B n b s f x).
Proof. exact (MK_COMB (@lem3812082 B) (@lem3812081 A B n x f b g s h1)). Qed.
Lemma lem3812088 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : @IN A x s) : (term237 A B b n g s f x) = (term246 A B n b s f x).
Proof. exact (MK_COMB (@lem3812062 A x s h2) (@lem3812083 A B n x f b g s h1)). Qed.
Lemma lem3812090 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3812091 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) : (term246 A B n b s f x) = (term245 A B n b s f x).
Proof. exact (@lem3812090 (term245 A B n b s f x)). Qed.
Lemma lem3812102 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : @IN A x s) : (term237 A B b n g s f x) = (term245 A B n b s f x).
Proof. exact (TRANS (@lem3812088 A B n f b g x s h1 h2) (@lem3812091 A B n b s f x)). Qed.
Lemma lem3812103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3812104 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : @IN A x s) : (term247 A B b n g s f x) = (term248 A B n b s f x).
Proof. exact (MK_COMB (@lem3812103) (@lem3812102 A B n f b g x s h1 h2)). Qed.
Lemma lem3812109 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term140 A B b f g s x) = (term140 A B b f g s x).
Proof. exact (eq_refl (term140 A B b f g s x)). Qed.
Lemma lem3812110 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : @IN A x s) : (term249 A B n b f g s x) = (term250 A B n b f g s x).
Proof. exact (MK_COMB (@lem3812104 A B n f b g x s h1 h2) (@lem3812109 A B b f g s x)). Qed.
Lemma lem3812113 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : @IN A x s) : (term250 A B n b f g s x) = (term249 A B n b f g s x).
Proof. exact (SYM (@lem3812110 A B n f b g x s h1 h2)). Qed.
Lemma lem3812114 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (h1 : term245 A B n b s f x) : term245 A B n b s f x.
Proof. exact (h1). Qed.
Lemma lem3812115 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term241 A B n b s f x w) : term241 A B n b s f x w.
Proof. exact (h1). Qed.
Lemma lem3812116 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term238 A B b s f x w) : term238 A B b s f x w.
Proof. exact (h1). Qed.
Lemma lem3812117 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term251 A B f b s x w n) : term251 A B f b s x w n.
Proof. exact (h1). Qed.
Lemma lem3812118 {A B : Type'} (g : type685 A B) (s : A -> Prop) (x : A) (w : B) (h1 : (term203 A B g s x) = w) : (term203 A B g s x) = w.
Proof. exact (h1). Qed.
Lemma lem3812119 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) : (term252 A B b s f x) = (term252 A B b s f x).
Proof. exact (eq_refl (term252 A B b s f x)). Qed.
Lemma lem3812120 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) (w : B) (h1 : (term203 A B g s x) = w) : (term253 A B b f g s x) = (term254 A B b s f x w).
Proof. exact (MK_COMB (@lem3812119 A B b s f x) (@lem3812118 A B g s x w h1)). Qed.
Lemma lem3812121 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) : (term254 A B b s f x w) = (term238 A B b s f x w).
Proof. exact (eq_refl (term254 A B b s f x w)). Qed.
Lemma lem3812122 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term255 A B b f g s x) = (term255 A B b f g s x).
Proof. exact (eq_refl (term255 A B b f g s x)). Qed.
Lemma lem3812123 {A B : Type'} (g : type685 A B) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) : ((term253 A B b f g s x) = (term254 A B b s f x w)) = ((term253 A B b f g s x) = (term238 A B b s f x w)).
Proof. exact (MK_COMB (@lem3812122 A B b f g s x) (@lem3812121 A B b s f x w)). Qed.
Lemma lem3812124 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term253 A B b f g s x) = (term140 A B b f g s x).
Proof. exact (eq_refl (term253 A B b f g s x)). Qed.
Lemma lem3812125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3812126 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term255 A B b f g s x) = (term256 A B b f g s x).
Proof. exact (MK_COMB (@lem3812125) (@lem3812124 A B b f g s x)). Qed.
Lemma lem3812127 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) : (term238 A B b s f x w) = (term238 A B b s f x w).
Proof. exact (eq_refl (term238 A B b s f x w)). Qed.
Lemma lem3812128 {A B : Type'} (g : type685 A B) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) : ((term253 A B b f g s x) = (term238 A B b s f x w)) = ((term140 A B b f g s x) = (term238 A B b s f x w)).
Proof. exact (MK_COMB (@lem3812126 A B b f g s x) (@lem3812127 A B b s f x w)). Qed.
Lemma lem3812129 {A B : Type'} (g : type685 A B) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) : ((term253 A B b f g s x) = (term254 A B b s f x w)) = ((term140 A B b f g s x) = (term238 A B b s f x w)).
Proof. exact (TRANS (@lem3812123 A B g b s f x w) (@lem3812128 A B g b s f x w)). Qed.
Lemma lem3812130 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) (w : B) (h1 : (term203 A B g s x) = w) : (term140 A B b f g s x) = (term238 A B b s f x w).
Proof. exact (EQ_MP (@lem3812129 A B g b s f x w) (@lem3812120 A B b f g s x w h1)). Qed.
Lemma lem3812131 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) (w : B) (h1 : (term203 A B g s x) = w) : (term238 A B b s f x w) = (term140 A B b f g s x).
Proof. exact (SYM (@lem3812130 A B b f g s x w h1)). Qed.
Lemma lem3812132 {A : Type'} (s : A -> Prop) (x : A) (h1 : term257 A s x) : term257 A s x.
Proof. exact (h1). Qed.
Lemma lem3812134 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3811224 A s) (@lem3811223 A s)). Qed.
Lemma lem3812135 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3812134 A s). Qed.
Lemma lem3812136 {A : Type'} (s : A -> Prop) (x : A) : term258 A s x.
Proof. exact (@lem3812135 A (@DELETE A s x)). Qed.
Lemma lem3812156 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3812186 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3812156 A s) (@lem3811490 A s h1)). Qed.
Lemma lem3812187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3812188 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term259 A s) = (and True).
Proof. exact (MK_COMB (@lem3812187) (@lem3812186 A s h1)). Qed.
Lemma lem3812189 {A : Type'} (x : A) (s : A -> Prop) : (term260 A x s) = (term260 A x s).
Proof. exact (eq_refl (term260 A x s)). Qed.
Lemma lem3812190 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term261 A x s) = (term262 A x s).
Proof. exact (MK_COMB (@lem3812188 A s h1) (@lem3812189 A x s)). Qed.
Lemma lem3812192 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3812193 {A : Type'} (x : A) (s : A -> Prop) : (term262 A x s) = (term260 A x s).
Proof. exact (@lem3812192 (term260 A x s)). Qed.
Lemma lem3812194 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term261 A x s) = (term260 A x s).
Proof. exact (TRANS (@lem3812190 A x s h1) (@lem3812193 A x s)). Qed.
Lemma lem3812195 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term260 A x s) = (term261 A x s).
Proof. exact (SYM (@lem3812194 A x s h1)). Qed.
Lemma lem3812197 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term263 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3812198 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term263 A s t).
Proof. exact (@lem3812197 A s t). Qed.
Lemma lem3812199 {A : Type'} (x : A) (s : A -> Prop) : (term260 A x s) = (term264 A x s).
Proof. exact (@lem3812198 A (@DELETE A s x) s). Qed.
Lemma lem3812206 {A : Type'} (x : A) (s : A -> Prop) : (term264 A x s) = (term260 A x s).
Proof. exact (SYM (@lem3812199 A x s)). Qed.
Lemma lem3812214 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term265 A x s y) = (term266 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3812215 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term265 A x s y) = (term266 A s x y).
Proof. exact (@lem3812214 A s x y). Qed.
Lemma lem3812216 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term265 A x' s x) = (term266 A s x' x).
Proof. exact (@lem3812215 A s x' x). Qed.
Lemma lem3812220 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3812221 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3812220 A P x). Qed.
Lemma lem3812222 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3812221 A s x'). Qed.
Lemma lem3812223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3812224 {A : Type'} (s : A -> Prop) (x' : A) : (term267 A x' s) = (term268 A s x').
Proof. exact (MK_COMB (@lem3812223) (@lem3812222 A s x')). Qed.
Lemma lem3812227 {A : Type'} (x' : A) (x : A) : (term269 A x' x) = (term269 A x' x).
Proof. exact (eq_refl (term269 A x' x)). Qed.
Lemma lem3812228 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term266 A s x' x) = (term270 A s x' x).
Proof. exact (MK_COMB (@lem3812224 A s x') (@lem3812227 A x' x)). Qed.
Lemma lem3812231 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term265 A x' s x) = (term270 A s x' x).
Proof. exact (TRANS (@lem3812216 A s x' x) (@lem3812228 A s x' x)). Qed.
Lemma lem3812232 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3812233 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term271 A x' s x) = (term272 A s x' x).
Proof. exact (MK_COMB (@lem3812232) (@lem3812231 A s x' x)). Qed.
Lemma lem3812235 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3812236 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3812235 A P x). Qed.
Lemma lem3812237 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3812236 A s x'). Qed.
Lemma lem3812238 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term273 A x x' s) = (term274 A x s x').
Proof. exact (MK_COMB (@lem3812233 A s x' x) (@lem3812237 A s x')). Qed.
Lemma lem3812241 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term276 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3812238 A x s x')). Qed.
Lemma lem3812242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3812243 {A : Type'} (x : A) (s : A -> Prop) : (term264 A x s) = (term277 A x s).
Proof. exact (MK_COMB (@lem3812242 A) (@lem3812241 A x s)). Qed.
Lemma lem3812248 {A : Type'} (x : A) (s : A -> Prop) : (term277 A x s) = (term264 A x s).
Proof. exact (SYM (@lem3812243 A x s)). Qed.
Lemma lem3812250 (p : Prop) : p = (term278 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3812251 {A : Type'} (x : A) (s : A -> Prop) : (term277 A x s) = (term279 A x s).
Proof. exact (@lem3812250 (term277 A x s)). Qed.
Lemma lem3812252 {A : Type'} (x : A) (s : A -> Prop) : (term279 A x s) = (term277 A x s).
Proof. exact (SYM (@lem3812251 A x s)). Qed.
Lemma lem3812253 {A : Type'} (x : A) (s : A -> Prop) (h1 : term280 A x s) : term280 A x s.
Proof. exact (h1). Qed.
Lemma lem3812256 {A : Type'} (x : A) (s : A -> Prop) (h1 : term279 A x s) : term279 A x s.
Proof. exact (h1). Qed.
Lemma lem3812257 {A : Type'} (x : A) (s : A -> Prop) : term281 A x s.
Proof. exact (fun h0 : term279 A x s => @lem3812256 A x s h0). Qed.
Lemma lem3812258 {A : Type'} (x : A) (s : A -> Prop) (h1 : term281 A x s) : term281 A x s.
Proof. exact (h1). Qed.
Lemma lem3812259 {A : Type'} (x : A) (s : A -> Prop) (h1 : term279 A x s) : term279 A x s.
Proof. exact (h1). Qed.
Lemma lem3812260 {A : Type'} (x : A) (s : A -> Prop) (h1 : term279 A x s) (h2 : term281 A x s) : term279 A x s.
Proof. exact (@lem3812258 A x s h2 (@lem3812259 A x s h1)). Qed.
Lemma lem3812261 {A : Type'} (x : A) (s : A -> Prop) (h1 : term279 A x s) : term282 A x s.
Proof. exact (fun h0 : term281 A x s => @lem3812260 A x s h1 h0). Qed.
Lemma lem3812262 {A : Type'} (x : A) (s : A -> Prop) (h1 : term281 A x s) : term281 A x s.
Proof. exact (h1). Qed.
Lemma lem3812263 {A : Type'} (x : A) (s : A -> Prop) (h1 : term279 A x s) (h2 : term281 A x s) : term279 A x s.
Proof. exact (@lem3812261 A x s h1 (@lem3812262 A x s h2)). Qed.
Lemma lem3812264 {A : Type'} (x : A) (s : A -> Prop) (h1 : term281 A x s) : term281 A x s.
Proof. exact (fun h0 : term279 A x s => @lem3812263 A x s h0 h1). Qed.
Lemma lem3812265 {A : Type'} (x : A) (s : A -> Prop) : term283 A x s.
Proof. exact (fun h0 : term281 A x s => @lem3812264 A x s h0). Qed.
Lemma lem3812268 {A : Type'} (x : A) (s : A -> Prop) : term281 A x s.
Proof. exact (@lem3812265 A x s (@lem3812257 A x s)). Qed.
Lemma lem3812269 {A : Type'} (x : A) (s : A -> Prop) : term281 A x s.
Proof. exact (@lem3812268 A x s). Qed.
Lemma lem3812279 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3812280 {A : Type'} (x : A) (s : A -> Prop) : (term279 A x s) = (term284 A x s).
Proof. exact (@lem3812279 (term280 A x s)). Qed.
Lemma lem3812282 (t : Prop) : (term285 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3812283 {A : Type'} (x : A) (s : A -> Prop) : (term284 A x s) = (term277 A x s).
Proof. exact (@lem3812282 (term277 A x s)). Qed.
Lemma lem3812288 {A : Type'} (x : A) (s : A -> Prop) : (term279 A x s) = (term277 A x s).
Proof. exact (TRANS (@lem3812280 A x s) (@lem3812283 A x s)). Qed.
Lemma lem3812293 {A : Type'} (s : A -> Prop) : (term286 A s) = (term287 A s).
Proof. exact (fun_ext (fun x : A => @lem3812288 A x s)). Qed.
Lemma lem3812294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3812295 {A : Type'} (s : A -> Prop) : (term288 A s) = (term289 A s).
Proof. exact (MK_COMB (@lem3812294 A) (@lem3812293 A s)). Qed.
Lemma lem3812300 {A : Type'} : (term290 A) = (term291 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3812295 A s)). Qed.
Lemma lem3812301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3812310 {A : Type'} : (term292 A) = (term293 A).
Proof. exact (MK_COMB (@lem3812301 A) (@lem3812300 A)). Qed.
Lemma lem3812321 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term274 A x s x') = (term274 A x s x').
Proof. exact (eq_refl (term274 A x s x')). Qed.
Lemma lem3812322 {A : Type'} (x : A) (s : A -> Prop) : (term276 A x s) = (term276 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3812321 A x s x')). Qed.
Lemma lem3812323 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3812324 {A : Type'} (x : A) (s : A -> Prop) : (term277 A x s) = (term277 A x s).
Proof. exact (MK_COMB (@lem3812323 A) (@lem3812322 A x s)). Qed.
Lemma lem3812325 {A : Type'} (s : A -> Prop) : (term287 A s) = (term287 A s).
Proof. exact (fun_ext (fun x : A => @lem3812324 A x s)). Qed.
Lemma lem3812326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3812327 {A : Type'} (s : A -> Prop) : (term289 A s) = (term289 A s).
Proof. exact (MK_COMB (@lem3812326 A) (@lem3812325 A s)). Qed.
Lemma lem3812328 {A : Type'} : (term291 A) = (term291 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3812327 A s)). Qed.
Lemma lem3812329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3812330 {A : Type'} : (term293 A) = (term293 A).
Proof. exact (MK_COMB (@lem3812329 A) (@lem3812328 A)). Qed.
Lemma lem3812355 {A : Type'} : (term292 A) = (term293 A).
Proof. exact (TRANS (@lem3812310 A) (@lem3812330 A)). Qed.
Lemma lem3812356 {A : Type'} : (term293 A) = (term292 A).
Proof. exact (SYM (@lem3812355 A)). Qed.
Lemma lem3812359 (p : Prop) : p = (term278 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3812360 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (term294 A s x').
Proof. exact (@lem3812359 (s x')). Qed.
Lemma lem3812361 {A : Type'} (s : A -> Prop) (x' : A) : (term294 A s x') = (s x').
Proof. exact (SYM (@lem3812360 A s x')). Qed.
Lemma lem3812362 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term295 A s x') : term295 A s x'.
Proof. exact (h1). Qed.
Lemma lem3812372 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : term270 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3812378 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term295 A s x') : term295 A s x'.
Proof. exact (h1). Qed.
Lemma lem3812392 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : term270 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3812398 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term295 A s x') : term295 A s x'.
Proof. exact (h1). Qed.
Lemma lem3812404 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term295 A s x') : term295 A s x'.
Proof. exact (h1). Qed.
Lemma lem3812414 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term295 A s x') : term295 A s x'.
Proof. exact (h1). Qed.
Lemma lem3812434 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : s x'.
Proof. exact (proj1 (@lem3812392 A s x' x h1)). Qed.
Lemma lem3812435 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : term296 A s x'.
Proof. exact (fun h0 : term295 A s x' => @lem3812434 A s x' x h1). Qed.
Lemma lem3812437 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3812438 {A : Type'} (s : A -> Prop) (x' : A) : (term296 A s x') = (s x').
Proof. exact (@lem3812437 (s x')). Qed.
Lemma lem3812439 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3812438 A s x') (@lem3812435 A s x' x h1)). Qed.
Lemma lem3812442 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3812444 {A : Type'} (s : A -> Prop) (x' : A) : (term295 A s x') = (term298 A s x').
Proof. exact (@lem3812442 (s x')). Qed.
Lemma lem3812447 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term295 A s x') : term298 A s x'.
Proof. exact (EQ_MP (@lem3812444 A s x') (@lem3812414 A s x' h1)). Qed.
Lemma lem3812450 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (@lem3812447 A s x' h1 (@lem3812439 A s x' x h2)). Qed.
Lemma lem3812451 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : term299.
Proof. exact (fun h0 : ~ False => @lem3812450 A s x' x h1 h2). Qed.
Lemma lem3812453 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3812454 : term299 = False.
Proof. exact (@lem3812453 False). Qed.
Lemma lem3812455 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812454) (@lem3812451 A s x' x h1 h2)). Qed.
Lemma lem3812456 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term295 A s x') = False.
Proof. exact (prop_ext (fun h3 : term295 A s x' => @lem3812455 A s x' x h1 h2) (fun h3 : False => @lem3812414 A s x' h1)). Qed.
Lemma lem3812457 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812456 A s x' x h1 h2) (@lem3812414 A s x' h1)). Qed.
Lemma lem3812458 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term295 A s x') = False.
Proof. exact (prop_ext (fun h3 : term295 A s x' => @lem3812457 A s x' x h1 h2) (fun h3 : False => @lem3812404 A s x' h1)). Qed.
Lemma lem3812459 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812458 A s x' x h1 h2) (@lem3812404 A s x' h1)). Qed.
Lemma lem3812460 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term295 A s x') = False.
Proof. exact (prop_ext (fun h3 : term295 A s x' => @lem3812459 A s x' x h1 h2) (fun h3 : False => @lem3812404 A s x' h1)). Qed.
Lemma lem3812461 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812460 A s x' x h1 h2) (@lem3812404 A s x' h1)). Qed.
Lemma lem3812462 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term295 A s x') = False.
Proof. exact (prop_ext (fun h3 : term295 A s x' => @lem3812461 A s x' x h1 h2) (fun h3 : False => @lem3812398 A s x' h1)). Qed.
Lemma lem3812463 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812462 A s x' x h1 h2) (@lem3812398 A s x' h1)). Qed.
Lemma lem3812464 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term270 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term270 A s x' x => @lem3812463 A s x' x h1 h2) (fun h3 : False => @lem3812392 A s x' x h2)). Qed.
Lemma lem3812465 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812464 A s x' x h1 h2) (@lem3812392 A s x' x h2)). Qed.
Lemma lem3812466 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term295 A s x') = False.
Proof. exact (prop_ext (fun h3 : term295 A s x' => @lem3812465 A s x' x h1 h2) (fun h3 : False => @lem3812378 A s x' h1)). Qed.
Lemma lem3812467 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812466 A s x' x h1 h2) (@lem3812378 A s x' h1)). Qed.
Lemma lem3812468 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term270 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term270 A s x' x => @lem3812467 A s x' x h1 h2) (fun h3 : False => @lem3812372 A s x' x h2)). Qed.
Lemma lem3812469 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812468 A s x' x h1 h2) (@lem3812372 A s x' x h2)). Qed.
Lemma lem3812470 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : (term295 A s x') = False.
Proof. exact (prop_ext (fun h3 : term295 A s x' => @lem3812469 A s x' x h1 h2) (fun h3 : False => @lem3812362 A s x' h1)). Qed.
Lemma lem3812471 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term295 A s x') (h2 : term270 A s x' x) : False.
Proof. exact (EQ_MP (@lem3812470 A s x' x h1 h2) (@lem3812362 A s x' h1)). Qed.
Lemma lem3812472 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : term294 A s x'.
Proof. exact (fun h0 : term295 A s x' => @lem3812471 A s x' x h0 h1). Qed.
Lemma lem3812473 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term270 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3812361 A s x') (@lem3812472 A s x' x h1)). Qed.
Lemma lem3812474 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : term274 A x s x'.
Proof. exact (fun h0 : term270 A s x' x => @lem3812473 A s x' x h0). Qed.
Lemma lem3812479 {A : Type'} (x : A) (s : A -> Prop) : term277 A x s.
Proof. exact (fun x' : A => @lem3812474 A x s x'). Qed.
Lemma lem3812484 {A : Type'} (s : A -> Prop) : term289 A s.
Proof. exact (fun x : A => @lem3812479 A x s). Qed.
Lemma lem3812489 {A : Type'} : term293 A.
Proof. exact (fun s : A -> Prop => @lem3812484 A s). Qed.
Lemma lem3812490 {A : Type'} : term292 A.
Proof. exact (EQ_MP (@lem3812356 A) (@lem3812489 A)). Qed.
Lemma lem3812491 {A : Type'} (s : A -> Prop) : term300 A s.
Proof. exact (@lem3812490 A s). Qed.
Lemma lem3812492 {A : Type'} (s : A -> Prop) : (term300 A s) = (term288 A s).
Proof. exact (eq_refl (term300 A s)). Qed.
Lemma lem3812493 {A : Type'} (s : A -> Prop) : term288 A s.
Proof. exact (EQ_MP (@lem3812492 A s) (@lem3812491 A s)). Qed.
Lemma lem3812494 {A : Type'} (s : A -> Prop) (x : A) : term301 A s x.
Proof. exact (@lem3812493 A s x). Qed.
Lemma lem3812495 {A : Type'} (x : A) (s : A -> Prop) : (term301 A s x) = (term279 A x s).
Proof. exact (eq_refl (term301 A s x)). Qed.
Lemma lem3812496 {A : Type'} (x : A) (s : A -> Prop) : term279 A x s.
Proof. exact (EQ_MP (@lem3812495 A x s) (@lem3812494 A s x)). Qed.
Lemma lem3812498 {A : Type'} (x : A) (s : A -> Prop) : term279 A x s.
Proof. exact (@lem3812269 A x s (@lem3812496 A x s)). Qed.
Lemma lem3812499 {A : Type'} (x : A) (s : A -> Prop) (h1 : term280 A x s) : False.
Proof. exact (@lem3812498 A x s (@lem3812253 A x s h1)). Qed.
Lemma lem3812500 {A : Type'} (x : A) (s : A -> Prop) (h1 : term280 A x s) : (term280 A x s) = False.
Proof. exact (prop_ext (fun h2 : term280 A x s => @lem3812499 A x s h1) (fun h2 : False => @lem3812253 A x s h1)). Qed.
Lemma lem3812501 {A : Type'} (x : A) (s : A -> Prop) (h1 : term280 A x s) : False.
Proof. exact (EQ_MP (@lem3812500 A x s h1) (@lem3812253 A x s h1)). Qed.
Lemma lem3812502 {A : Type'} (x : A) (s : A -> Prop) : term279 A x s.
Proof. exact (fun h0 : term280 A x s => @lem3812501 A x s h0). Qed.
Lemma lem3812503 {A : Type'} (x : A) (s : A -> Prop) : term277 A x s.
Proof. exact (EQ_MP (@lem3812252 A x s) (@lem3812502 A x s)). Qed.
Lemma lem3812504 {A : Type'} (x : A) (s : A -> Prop) : term264 A x s.
Proof. exact (EQ_MP (@lem3812248 A x s) (@lem3812503 A x s)). Qed.
Lemma lem3812505 {A : Type'} (x : A) (s : A -> Prop) : term260 A x s.
Proof. exact (EQ_MP (@lem3812206 A x s) (@lem3812504 A x s)). Qed.
Lemma lem3812506 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term261 A x s.
Proof. exact (EQ_MP (@lem3812195 A x s h1) (@lem3812505 A x s)). Qed.
Lemma lem3812507 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term302 A s x.
Proof. exact (ex_intro (term303 A s x) s (@lem3812506 A x s h1)). Qed.
Lemma lem3812508 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term257 A s x.
Proof. exact (@lem3812136 A s x (@lem3812507 A x s h1)). Qed.
Lemma lem3812509 {A : Type'} (s : A -> Prop) (x : A) (h1 : term257 A s x) : term257 A s x.
Proof. exact (h1). Qed.
Lemma lem3812536 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term107 A B f b g.
Proof. exact (h1). Qed.
Lemma lem3812537 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term113 A B f b g s.
Proof. exact (@lem3812536 A B f b g h1 s). Qed.
Lemma lem3812538 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term113 A B f b g s) = (term103 A B f b g s).
Proof. exact (eq_refl (term113 A B f b g s)). Qed.
Lemma lem3812539 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term103 A B f b g s.
Proof. exact (EQ_MP (@lem3812538 A B f b g s) (@lem3812537 A B s f b g h1)). Qed.
Lemma lem3812540 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term114 A B f b g s a.
Proof. exact (@lem3812539 A B s f b g h1 a). Qed.
Lemma lem3812541 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (a : B) : (term114 A B f b g s a) = (term99 A B f b g s a).
Proof. exact (eq_refl (term114 A B f b g s a)). Qed.
Lemma lem3812542 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term99 A B f b g s a.
Proof. exact (EQ_MP (@lem3812541 A B f b g s a) (@lem3812540 A B s a f b g h1)). Qed.
Lemma lem3812543 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3812544 {A B : Type'} (a : B) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : (term52 A B f b s a) = ((g s) = a).
Proof. exact (@lem3812542 A B s a f b g h1 (@lem3812543 A s h2)). Qed.
Lemma lem3812545 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : term115 A B f b g s.
Proof. exact (fun a : B => @lem3812544 A B a f b g s h1 h2). Qed.
Lemma lem3812546 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (fun h0 : @FINITE A s => @lem3812545 A B f b g s h1 h0). Qed.
Lemma lem3812547 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term117 A B f b g.
Proof. exact (fun s : A -> Prop => @lem3812546 A B s f b g h1). Qed.
Lemma lem3812548 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) : term118 A B f b g.
Proof. exact (fun h0 : term107 A B f b g => @lem3812547 A B f b g h0). Qed.
Lemma lem3812549 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term117 A B f b g.
Proof. exact (@lem3812548 A B f b g (@lem3811388 A B f b g h1)). Qed.
Lemma lem3812550 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term119 A B f b g s.
Proof. exact (@lem3812549 A B f b g h1 s). Qed.
Lemma lem3812551 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) : (term119 A B f b g s) = (term116 A B f b g s).
Proof. exact (eq_refl (term119 A B f b g s)). Qed.
Lemma lem3812554 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (EQ_MP (@lem3812551 A B f b g s) (@lem3812550 A B s f b g h1)). Qed.
Lemma lem3812555 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term116 A B f b g s.
Proof. exact (@lem3812554 A B s f b g h1). Qed.
Lemma lem3812556 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term107 A B f b g) : term304 A B f b g s x.
Proof. exact (@lem3812555 A B (@DELETE A s x) f b g h1). Qed.
Lemma lem3812557 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (x : A) (h1 : term107 A B f b g) (h2 : term257 A s x) : term305 A B f b g s x.
Proof. exact (@lem3812556 A B s x f b g h1 (@lem3812509 A s x h2)). Qed.
Lemma lem3812559 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (x : A) (a : B) (h1 : (term306 A B f b s x a) = ((term203 A B g s x) = a)) : (term306 A B f b s x a) = ((term203 A B g s x) = a).
Proof. exact (h1). Qed.
Lemma lem3812560 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (x : A) (a : B) (h1 : (term306 A B f b s x a) = ((term203 A B g s x) = a)) : ((term203 A B g s x) = a) = (term306 A B f b s x a).
Proof. exact (SYM (@lem3812559 A B f b g s x a h1)). Qed.
Lemma lem3812561 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (a : B) (h1 : ((term203 A B g s x) = a) = (term306 A B f b s x a)) : ((term203 A B g s x) = a) = (term306 A B f b s x a).
Proof. exact (h1). Qed.
Lemma lem3812562 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (a : B) (h1 : ((term203 A B g s x) = a) = (term306 A B f b s x a)) : (term306 A B f b s x a) = ((term203 A B g s x) = a).
Proof. exact (SYM (@lem3812561 A B g f b s x a h1)). Qed.
Lemma lem3812563 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (a : B) : ((term306 A B f b s x a) = ((term203 A B g s x) = a)) = (((term203 A B g s x) = a) = (term306 A B f b s x a)).
Proof. exact (prop_ext (fun h1 : (term306 A B f b s x a) = ((term203 A B g s x) = a) => @lem3812560 A B f b g s x a h1) (fun h1 : ((term203 A B g s x) = a) = (term306 A B f b s x a) => @lem3812562 A B g f b s x a h1)). Qed.
Lemma lem3812564 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term307 A B f b g s x) = (term308 A B g f b s x).
Proof. exact (fun_ext (fun a : B => @lem3812563 A B g f b s x a)). Qed.
Lemma lem3812565 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3812566 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term305 A B f b g s x) = (term309 A B g f b s x).
Proof. exact (MK_COMB (@lem3812565 B) (@lem3812564 A B g f b s x)). Qed.
Lemma lem3812567 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (x : A) (h1 : term107 A B f b g) (h2 : term257 A s x) : term309 A B g f b s x.
Proof. exact (EQ_MP (@lem3812566 A B g f b s x) (@lem3812557 A B f b g s x h1 h2)). Qed.
Lemma lem3812584 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term309 A B g f b s x) : term309 A B g f b s x.
Proof. exact (h1). Qed.
Lemma lem3812585 {A B : Type'} (a : B) (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term309 A B g f b s x) : term310 A B g f b s x a.
Proof. exact (@lem3812584 A B g f b s x h1 a). Qed.
Lemma lem3812586 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (a : B) : (term310 A B g f b s x a) = (((term203 A B g s x) = a) = (term306 A B f b s x a)).
Proof. exact (eq_refl (term310 A B g f b s x a)). Qed.
Lemma lem3812589 {A B : Type'} (a : B) (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term309 A B g f b s x) : ((term203 A B g s x) = a) = (term306 A B f b s x a).
Proof. exact (EQ_MP (@lem3812586 A B g f b s x a) (@lem3812585 A B a g f b s x h1)). Qed.
Lemma lem3812590 {A B : Type'} (a : B) (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term309 A B g f b s x) : ((term203 A B g s x) = a) = (term306 A B f b s x a).
Proof. exact (@lem3812589 A B a g f b s x h1). Qed.
Lemma lem3812591 {A B : Type'} (w : B) (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term309 A B g f b s x) : ((term203 A B g s x) = w) = (term306 A B f b s x w).
Proof. exact (@lem3812590 A B w g f b s x h1). Qed.
Lemma lem3812596 {A B : Type'} (w : B) (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term309 A B g f b s x) : (term306 A B f b s x w) = ((term203 A B g s x) = w).
Proof. exact (SYM (@lem3812591 A B w g f b s x h1)). Qed.
Lemma lem3812639 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) : (term251 A B f b s x w n) = ((term251 A B f b s x w n) = True).
Proof. exact (@lem7 (term251 A B f b s x w n)). Qed.
Lemma lem3812644 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term251 A B f b s x w n) : (term251 A B f b s x w n) = True.
Proof. exact (EQ_MP (@lem3812639 A B f b s x w n) (@lem3812117 A B f b s x w n h1)). Qed.
Lemma lem3812645 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term251 A B f b s x w n) : True = (term251 A B f b s x w n).
Proof. exact (SYM (@lem3812644 A B f b s x w n h1)). Qed.
Lemma lem3812646 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term251 A B f b s x w n) : term251 A B f b s x w n.
Proof. exact (EQ_MP (@lem3812645 A B f b s x w n h1) (@lem0)). Qed.
Lemma lem3812647 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term251 A B f b s x w n) : term306 A B f b s x w.
Proof. exact (ex_intro (term311 A B f b s x w) n (@lem3812646 A B f b s x w n h1)). Qed.
Lemma lem3812648 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term309 A B g f b s x) (h2 : term251 A B f b s x w n) : (term203 A B g s x) = w.
Proof. exact (EQ_MP (@lem3812596 A B w g f b s x h1) (@lem3812647 A B f b s x w n h2)). Qed.
Lemma lem3812649 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term251 A B f b s x w n) : term312 A B f b g s x w.
Proof. exact (fun h0 : term309 A B g f b s x => @lem3812648 A B g f b s x w n h0 h1). Qed.
Lemma lem3812650 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term257 A s x) (h3 : term251 A B f b s x w n) : (term203 A B g s x) = w.
Proof. exact (@lem3812649 A B g f b s x w n h3 (@lem3812567 A B f b g s x h1 h2)). Qed.
Lemma lem3812651 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term251 A B f b s x w n) : term313 A B g s x w.
Proof. exact (fun h0 : term257 A s x => @lem3812650 A B g f b s x w n h1 h0 h2). Qed.
Lemma lem3812652 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term257 A s x) (h3 : term251 A B f b s x w n) : (term203 A B g s x) = w.
Proof. exact (@lem3812651 A B g f b s x w n h1 h3 (@lem3812132 A s x h2)). Qed.
Lemma lem3812653 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : @FINITE A s) (h3 : term251 A B f b s x w n) : (term257 A s x) = ((term203 A B g s x) = w).
Proof. exact (prop_ext (fun h4 : term257 A s x => @lem3812652 A B g f b s x w n h1 h4 h3) (fun h4 : (term203 A B g s x) = w => @lem3812508 A x s h2)). Qed.
Lemma lem3812654 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : @FINITE A s) (h3 : term251 A B f b s x w n) : (term203 A B g s x) = w.
Proof. exact (EQ_MP (@lem3812653 A B g f b s x w n h1 h2 h3) (@lem3812508 A x s h2)). Qed.
Lemma lem3812699 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) : (term238 A B b s f x w) = ((term238 A B b s f x w) = True).
Proof. exact (@lem7 (term238 A B b s f x w)). Qed.
Lemma lem3812702 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term238 A B b s f x w) : (term238 A B b s f x w) = True.
Proof. exact (EQ_MP (@lem3812699 A B b s f x w) (@lem3812116 A B b s f x w h1)). Qed.
Lemma lem3812703 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term238 A B b s f x w) : True = (term238 A B b s f x w).
Proof. exact (SYM (@lem3812702 A B b s f x w h1)). Qed.
Lemma lem3812704 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term238 A B b s f x w) : term238 A B b s f x w.
Proof. exact (EQ_MP (@lem3812703 A B b s f x w h1) (@lem0)). Qed.
Lemma lem3812705 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) (w : B) (h1 : term238 A B b s f x w) (h2 : (term203 A B g s x) = w) : term140 A B b f g s x.
Proof. exact (EQ_MP (@lem3812131 A B b f g s x w h2) (@lem3812704 A B b s f x w h1)). Qed.
Lemma lem3812706 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term238 A B b s f x w) (h3 : @FINITE A s) (h4 : term251 A B f b s x w n) : ((term203 A B g s x) = w) = (term140 A B b f g s x).
Proof. exact (prop_ext (fun h5 : (term203 A B g s x) = w => @lem3812705 A B b f g s x w h2 h5) (fun h5 : term140 A B b f g s x => @lem3812654 A B g f b s x w n h1 h3 h4)). Qed.
Lemma lem3812707 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term238 A B b s f x w) (h3 : @FINITE A s) (h4 : term251 A B f b s x w n) : term140 A B b f g s x.
Proof. exact (EQ_MP (@lem3812706 A B g f b s x w n h1 h2 h3 h4) (@lem3812654 A B g f b s x w n h1 h3 h4)). Qed.
Lemma lem3812708 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term241 A B n b s f x w) : term238 A B b s f x w.
Proof. exact (proj2 (@lem3812115 A B n b s f x w h1)). Qed.
Lemma lem3812709 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term241 A B n b s f x w) : term251 A B f b s x w n.
Proof. exact (proj1 (@lem3812115 A B n b s f x w h1)). Qed.
Lemma lem3812710 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term238 A B b s f x w) (h3 : @FINITE A s) (h4 : term251 A B f b s x w n) : (term238 A B b s f x w) = (term140 A B b f g s x).
Proof. exact (prop_ext (fun h5 : term238 A B b s f x w => @lem3812707 A B g f b s x w n h1 h2 h3 h4) (fun h5 : term140 A B b f g s x => @lem3812116 A B b s f x w h2)). Qed.
Lemma lem3812711 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term238 A B b s f x w) (h3 : @FINITE A s) (h4 : term251 A B f b s x w n) : term140 A B b f g s x.
Proof. exact (EQ_MP (@lem3812710 A B g f b s x w n h1 h2 h3 h4) (@lem3812116 A B b s f x w h2)). Qed.
Lemma lem3812712 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term238 A B b s f x w) (h3 : @FINITE A s) (h4 : term251 A B f b s x w n) : (term251 A B f b s x w n) = (term140 A B b f g s x).
Proof. exact (prop_ext (fun h5 : term251 A B f b s x w n => @lem3812711 A B g f b s x w n h1 h2 h3 h4) (fun h5 : term140 A B b f g s x => @lem3812117 A B f b s x w n h4)). Qed.
Lemma lem3812713 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : term238 A B b s f x w) (h3 : @FINITE A s) (h4 : term251 A B f b s x w n) : term140 A B b f g s x.
Proof. exact (EQ_MP (@lem3812712 A B g f b s x w n h1 h2 h3 h4) (@lem3812117 A B f b s x w n h4)). Qed.
Lemma lem3812714 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : @FINITE A s) (h3 : term241 A B n b s f x w) (h4 : term251 A B f b s x w n) : (term238 A B b s f x w) = (term140 A B b f g s x).
Proof. exact (prop_ext (fun h5 : term238 A B b s f x w => @lem3812713 A B g f b s x w n h1 h5 h2 h4) (fun h5 : term140 A B b f g s x => @lem3812708 A B n b s f x w h3)). Qed.
Lemma lem3812715 {A B : Type'} (g : type685 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) (h1 : term107 A B f b g) (h2 : @FINITE A s) (h3 : term241 A B n b s f x w) (h4 : term251 A B f b s x w n) : term140 A B b f g s x.
Proof. exact (EQ_MP (@lem3812714 A B g f b s x w n h1 h2 h3 h4) (@lem3812708 A B n b s f x w h3)). Qed.
Lemma lem3812716 {A B : Type'} (g : type685 A B) (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term107 A B f b g) (h2 : @FINITE A s) (h3 : term241 A B n b s f x w) : (term251 A B f b s x w n) = (term140 A B b f g s x).
Proof. exact (prop_ext (fun h4 : term251 A B f b s x w n => @lem3812715 A B g f b s x w n h1 h2 h3 h4) (fun h4 : term140 A B b f g s x => @lem3812709 A B n b s f x w h3)). Qed.
Lemma lem3812717 {A B : Type'} (g : type685 A B) (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (w : B) (h1 : term107 A B f b g) (h2 : @FINITE A s) (h3 : term241 A B n b s f x w) : term140 A B b f g s x.
Proof. exact (EQ_MP (@lem3812716 A B g n b s f x w h1 h2 h3) (@lem3812709 A B n b s f x w h3)). Qed.
Lemma lem3812718 {A B : Type'} (g : type685 A B) (n : nat) (b : B) (f : type1411 A B) (x : A) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : term245 A B n b s f x) (h3 : @FINITE A s) : term140 A B b f g s x.
Proof. exact (ex_elim (@lem3812114 A B n b s f x h2) (fun w : B => fun h0 : term243 A B n b s f x w => @lem3812717 A B g n b s f x w h1 h3 h0)). Qed.
Lemma lem3812719 {A B : Type'} (n : nat) (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (h1 : term107 A B f b g) (h2 : @FINITE A s) : term250 A B n b f g s x.
Proof. exact (fun h0 : term245 A B n b s f x => @lem3812718 A B g n b f x s h1 h0 h2). Qed.
Lemma lem3812720 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term115 A B f b g s) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : term249 A B n b f g s x.
Proof. exact (EQ_MP (@lem3812113 A B n f b g x s h1 h4) (@lem3812719 A B n x f b g s h2 h3)). Qed.
Lemma lem3812721 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (s : A -> Prop) (n : nat) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) (h6 : term226 A B f b g s n) : term140 A B b f g s x.
Proof. exact (@lem3812720 A B n f b g x s h2 h3 h4 h5 (@lem3812012 A B x f b g s n h1 h6)). Qed.
Lemma lem3812722 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term177 A B n b f g s x.
Proof. exact (fun h0 : term226 A B f b g s n => @lem3812721 A B x f b g s n h1 h2 h3 h4 h5 h0). Qed.
Lemma lem3812723 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term179 A B n b f g s x.
Proof. exact (fun h0 : term163 A B n b f g s x => @lem3812722 A B n f b g x s h1 h2 h3 h4 h5). Qed.
Lemma lem3812728 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term183 A B b f g s x.
Proof. exact (fun n : nat => @lem3812723 A B n f b g x s h1 h2 h3 h4 h5). Qed.
Lemma lem3812729 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term185 A B b f g s x.
Proof. exact (conj (@lem3811828 A B f b g x s h2 h5) (@lem3812728 A B f b g x s h1 h2 h3 h4 h5)). Qed.
Lemma lem3812730 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term166 A B b f g s x.
Proof. exact (@lem3811681 A B b f g s x (@lem3812729 A B f b g x s h1 h2 h3 h4 h5)). Qed.
Lemma lem3812731 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term147 A B b f g s x.
Proof. exact (EQ_MP (@lem3811658 A B b f g s x) (@lem3812730 A B f b g x s h1 h2 h3 h4 h5)). Qed.
Lemma lem3812732 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term146 A B b f g s x.
Proof. exact (EQ_MP (@lem3811623 A B b f g s x) (@lem3812731 A B f b g x s h1 h2 h3 h4 h5)). Qed.
Lemma lem3812733 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : term140 A B b f g s x.
Proof. exact (@lem3812732 A B f b g x s h1 h2 h3 h4 h5 (@lem3811586 A B f b g s h2)). Qed.
Lemma lem3812734 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term115 A B f b g s) (h3 : term107 A B f b g) (h4 : @FINITE A s) (h5 : @IN A x s) : (g s) = (term139 A B f g s x).
Proof. exact (EQ_MP (@lem3811583 A B x f b g s h2) (@lem3812733 A B f b g x s h1 h2 h3 h4 h5)). Qed.
Lemma lem3812735 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : term314 A B b f g s x.
Proof. exact (fun h0 : term115 A B f b g s => @lem3812734 A B f b g x s h1 h0 h2 h3 h4). Qed.
Lemma lem3812736 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : (g s) = (term139 A B f g s x).
Proof. exact (@lem3812735 A B f b g x s h1 h2 h3 h4 (@lem3811537 A B f b g s h2 h3)). Qed.
Lemma lem3812737 {A : Type'} (x : A) (s : A -> Prop) (h1 : term134 A x s) : @IN A x s.
Proof. exact (proj2 (@lem3811488 A x s h1)). Qed.
Lemma lem3812738 {A : Type'} (x : A) (s : A -> Prop) (h1 : term134 A x s) : @FINITE A s.
Proof. exact (proj1 (@lem3811488 A x s h1)). Qed.
Lemma lem3812739 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : (@IN A x s) = ((g s) = (term139 A B f g s x)).
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem3812736 A B f b g x s h1 h2 h3 h4) (fun h5 : (g s) = (term139 A B f g s x) => @lem3811489 A x s h4)). Qed.
Lemma lem3812740 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : (g s) = (term139 A B f g s x).
Proof. exact (EQ_MP (@lem3812739 A B f b g x s h1 h2 h3 h4) (@lem3811489 A x s h4)). Qed.
Lemma lem3812741 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : (@FINITE A s) = ((g s) = (term139 A B f g s x)).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem3812740 A B f b g x s h1 h2 h3 h4) (fun h5 : (g s) = (term139 A B f g s x) => @lem3811490 A s h3)). Qed.
Lemma lem3812742 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : @IN A x s) : (g s) = (term139 A B f g s x).
Proof. exact (EQ_MP (@lem3812741 A B f b g x s h1 h2 h3 h4) (@lem3811490 A s h3)). Qed.
Lemma lem3812743 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : term134 A x s) : (@IN A x s) = ((g s) = (term139 A B f g s x)).
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem3812742 A B f b g x s h1 h2 h3 h5) (fun h5 : (g s) = (term139 A B f g s x) => @lem3812737 A x s h4)). Qed.
Lemma lem3812744 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : @FINITE A s) (h4 : term134 A x s) : (g s) = (term139 A B f g s x).
Proof. exact (EQ_MP (@lem3812743 A B f b g x s h1 h2 h3 h4) (@lem3812737 A x s h4)). Qed.
Lemma lem3812745 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : term134 A x s) : (@FINITE A s) = ((g s) = (term139 A B f g s x)).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3812744 A B f b g x s h1 h2 h4 h3) (fun h4 : (g s) = (term139 A B f g s x) => @lem3812738 A x s h3)). Qed.
Lemma lem3812746 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term26 A B f) (h2 : term107 A B f b g) (h3 : term134 A x s) : (g s) = (term139 A B f g s x).
Proof. exact (EQ_MP (@lem3812745 A B f b g x s h1 h2 h3) (@lem3812738 A x s h3)). Qed.
Lemma lem3812747 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term26 A B f) (h2 : term107 A B f b g) : term315 A B f g s x.
Proof. exact (fun h0 : term134 A x s => @lem3812746 A B f b g x s h1 h2 h0). Qed.
Lemma lem3812752 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term26 A B f) (h2 : term107 A B f b g) : term316 A B f g s.
Proof. exact (fun x : A => @lem3812747 A B s x f b g h1 h2). Qed.
Lemma lem3812757 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term26 A B f) (h2 : term107 A B f b g) : term317 A B f g.
Proof. exact (fun s : A -> Prop => @lem3812752 A B s f b g h1 h2). Qed.
Lemma lem3812758 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term26 A B f) (h2 : term107 A B f b g) : term318 A B b f g.
Proof. exact (conj (@lem3811487 A B f b g h2) (@lem3812757 A B f b g h1 h2)). Qed.
Lemma lem3812759 {A B : Type'} (f : type1411 A B) (b : B) (g : type685 A B) (h1 : term26 A B f) (h2 : term107 A B f b g) : term319 A B b f.
Proof. exact (ex_intro (term320 A B b f) g (@lem3812758 A B f b g h1 h2)). Qed.
Lemma lem3812760 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term26 A B f) (h2 : term111 A B f b) : term319 A B b f.
Proof. exact (ex_elim (@lem3811387 A B f b h2) (fun g : type685 A B => fun h0 : term109 A B f b g => @lem3812759 A B f b g h1 h0)). Qed.
Lemma lem3812761 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term321 A B b f.
Proof. exact (fun h0 : term111 A B f b => @lem3812760 A B f b h1 h0). Qed.
Lemma lem3812762 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term26 A B f) (h2 : term39 A B f b) : term319 A B b f.
Proof. exact (@lem3812761 A B b f h1 (@lem3811386 A B f b h2)). Qed.
Lemma lem3812763 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term322 A B b f.
Proof. exact (fun h0 : term39 A B f b => @lem3812762 A B f b h1 h0). Qed.
Lemma lem3812764 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term26 A B f) (h2 : term32 A B f b) : term319 A B b f.
Proof. exact (@lem3812763 A B b f h1 (@lem3811286 A B f b h2)). Qed.
Lemma lem3812765 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term323 A B b f.
Proof. exact (fun h0 : term32 A B f b => @lem3812764 A B f b h1 h0). Qed.
Lemma lem3812766 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) (h2 : term33 A B f) : term319 A B b f.
Proof. exact (@lem3812765 A B b f h1 (@lem3811284 A B b f h2)). Qed.
Lemma lem3812767 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term324 A B b f.
Proof. exact (fun h0 : term33 A B f => @lem3812766 A B b f h1 h0). Qed.
Lemma lem3812768 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term319 A B b f.
Proof. exact (@lem3812767 A B b f h1 (@lem3811280 A B f h1)). Qed.
Lemma lem3812769 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : (term26 A B f) = (term319 A B b f).
Proof. exact (prop_ext (fun h2 : term26 A B f => @lem3812768 A B b f h1) (fun h2 : term319 A B b f => @lem3811259 A B f h1)). Qed.
Lemma lem3812770 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term319 A B b f.
Proof. exact (EQ_MP (@lem3812769 A B b f h1) (@lem3811259 A B f h1)). Qed.
Lemma lem3812771 {A B : Type'} (b : B) (f : type1411 A B) : term325 A B b f.
Proof. exact (fun h0 : term26 A B f => @lem3812770 A B b f h0). Qed.
Lemma lem3812776 {A B : Type'} (f : type1411 A B) : term326 A B f.
Proof. exact (fun b : B => @lem3812771 A B b f). Qed.
Lemma lem3812781 {A B : Type'} : term327 A B.
Proof. exact (fun f : type1411 A B => @lem3812776 A B f). Qed.
