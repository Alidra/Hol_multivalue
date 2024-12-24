Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_MONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem4797008 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4797009 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4797010 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4797009 t1) (@lem4797008 t1)). Qed.
Lemma lem4797011 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4797010 t1 t2). Qed.
Lemma lem4797012 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4797013 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4797012 t1 t2) (@lem4797011 t1 t2)). Qed.
Lemma lem4797014 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4797013 t1 t2 t3). Qed.
Lemma lem4797015 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4797016 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4797015 t1 t2 t3) (@lem4797014 t1 t2 t3)). Qed.
Lemma lem4797017 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4797016 t1 t2 t3)). Qed.
Lemma lem4797018 {_110510 : Type'} (s : _110510 -> Prop) : term7 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4797019 {_110510 : Type'} (s : _110510 -> Prop) : (term7 _110510 s) = (term8 _110510 s).
Proof. exact (eq_refl (term7 _110510 s)). Qed.
Lemma lem4797020 {_110510 : Type'} (s : _110510 -> Prop) : term8 _110510 s.
Proof. exact (EQ_MP (@lem4797019 _110510 s) (@lem4797018 _110510 s)). Qed.
Lemma lem4797021 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term9 _110510 s r.
Proof. exact (@lem4797020 _110510 s r). Qed.
Lemma lem4797022 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term9 _110510 s r) = ((@pairwise _110510 r s) = (term10 _110510 s r)).
Proof. exact (eq_refl (term9 _110510 s r)). Qed.
Lemma lem4797041 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4797022 _110510 s r) (@lem4797021 _110510 s r)). Qed.
Lemma lem4797042 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (@pairwise _110613 r s) = (term10 _110613 s r).
Proof. exact (@lem4797041 _110613 s r). Qed.
Lemma lem4797059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797060 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term11 _110613 r s) = (term12 _110613 s r).
Proof. exact (MK_COMB (@lem4797059) (@lem4797042 _110613 s r)). Qed.
Lemma lem4797061 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (@SUBSET _110613 t s) = (@SUBSET _110613 t s).
Proof. exact (eq_refl (@SUBSET _110613 t s)). Qed.
Lemma lem4797062 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term13 _110613 r t s) = (term14 _110613 r t s).
Proof. exact (MK_COMB (@lem4797060 _110613 s r) (@lem4797061 _110613 t s)). Qed.
Lemma lem4797065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797066 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term15 _110613 r t s) = (term16 _110613 r t s).
Proof. exact (MK_COMB (@lem4797065) (@lem4797062 _110613 r t s)). Qed.
Lemma lem4797068 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4797022 _110510 s r) (@lem4797021 _110510 s r)). Qed.
Lemma lem4797069 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (@pairwise _110613 r s) = (term10 _110613 s r).
Proof. exact (@lem4797068 _110613 s r). Qed.
Lemma lem4797070 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) : (@pairwise _110613 r t) = (term10 _110613 t r).
Proof. exact (@lem4797069 _110613 t r). Qed.
Lemma lem4797087 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (r : type1402 _110613) : (term17 _110613 s r t) = (term18 _110613 s t r).
Proof. exact (MK_COMB (@lem4797066 _110613 r t s) (@lem4797070 _110613 t r)). Qed.
Lemma lem4797090 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term19 _110613 s r) = (term20 _110613 s r).
Proof. exact (fun_ext (fun t : _110613 -> Prop => @lem4797087 _110613 s t r)). Qed.
Lemma lem4797091 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797092 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term21 _110613 s r) = (term22 _110613 s r).
Proof. exact (MK_COMB (@lem4797091 _110613) (@lem4797090 _110613 s r)). Qed.
Lemma lem4797097 {_110613 : Type'} (r : type1402 _110613) : (term23 _110613 r) = (term24 _110613 r).
Proof. exact (fun_ext (fun s : _110613 -> Prop => @lem4797092 _110613 s r)). Qed.
Lemma lem4797098 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797099 {_110613 : Type'} (r : type1402 _110613) : (term25 _110613 r) = (term26 _110613 r).
Proof. exact (MK_COMB (@lem4797098 _110613) (@lem4797097 _110613 r)). Qed.
Lemma lem4797104 {_110613 : Type'} : (term27 _110613) = (term28 _110613).
Proof. exact (fun_ext (fun r : type1402 _110613 => @lem4797099 _110613 r)). Qed.
Lemma lem4797105 {_110613 : Type'} : (@all (_110613 -> _110613 -> Prop)) = (@all (_110613 -> _110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> _110613 -> Prop))). Qed.
Lemma lem4797106 {_110613 : Type'} : (term29 _110613) = (term30 _110613).
Proof. exact (MK_COMB (@lem4797105 _110613) (@lem4797104 _110613)). Qed.
Lemma lem4797111 {_110613 : Type'} : (term30 _110613) = (term29 _110613).
Proof. exact (SYM (@lem4797106 _110613)). Qed.
Lemma lem4797147 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4797148 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) : (@SUBSET _110613 s t) = (term31 _110613 s t).
Proof. exact (@lem4797147 _110613 s t). Qed.
Lemma lem4797149 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (@SUBSET _110613 t s) = (term31 _110613 t s).
Proof. exact (@lem4797148 _110613 t s). Qed.
Lemma lem4797156 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term12 _110613 s r) = (term12 _110613 s r).
Proof. exact (eq_refl (term12 _110613 s r)). Qed.
Lemma lem4797157 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term14 _110613 r t s) = (term32 _110613 r t s).
Proof. exact (MK_COMB (@lem4797156 _110613 s r) (@lem4797149 _110613 t s)). Qed.
Lemma lem4797160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797161 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term16 _110613 r t s) = (term33 _110613 r t s).
Proof. exact (MK_COMB (@lem4797160) (@lem4797157 _110613 r t s)). Qed.
Lemma lem4797180 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) : (term10 _110613 t r) = (term10 _110613 t r).
Proof. exact (eq_refl (term10 _110613 t r)). Qed.
Lemma lem4797181 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (r : type1402 _110613) : (term18 _110613 s t r) = (term34 _110613 s t r).
Proof. exact (MK_COMB (@lem4797161 _110613 r t s) (@lem4797180 _110613 t r)). Qed.
Lemma lem4797184 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term20 _110613 s r) = (term35 _110613 s r).
Proof. exact (fun_ext (fun t : _110613 -> Prop => @lem4797181 _110613 s t r)). Qed.
Lemma lem4797185 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797186 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term22 _110613 s r) = (term36 _110613 s r).
Proof. exact (MK_COMB (@lem4797185 _110613) (@lem4797184 _110613 s r)). Qed.
Lemma lem4797191 {_110613 : Type'} (r : type1402 _110613) : (term24 _110613 r) = (term37 _110613 r).
Proof. exact (fun_ext (fun s : _110613 -> Prop => @lem4797186 _110613 s r)). Qed.
Lemma lem4797192 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797193 {_110613 : Type'} (r : type1402 _110613) : (term26 _110613 r) = (term38 _110613 r).
Proof. exact (MK_COMB (@lem4797192 _110613) (@lem4797191 _110613 r)). Qed.
Lemma lem4797198 {_110613 : Type'} : (term28 _110613) = (term39 _110613).
Proof. exact (fun_ext (fun r : type1402 _110613 => @lem4797193 _110613 r)). Qed.
Lemma lem4797199 {_110613 : Type'} : (@all (_110613 -> _110613 -> Prop)) = (@all (_110613 -> _110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> _110613 -> Prop))). Qed.
Lemma lem4797200 {_110613 : Type'} : (term30 _110613) = (term40 _110613).
Proof. exact (MK_COMB (@lem4797199 _110613) (@lem4797198 _110613)). Qed.
Lemma lem4797205 {_110613 : Type'} : (term40 _110613) = (term30 _110613).
Proof. exact (SYM (@lem4797200 _110613)). Qed.
Lemma lem4797235 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4797236 {_110613 : Type'} (P : _110613 -> Prop) (x : _110613) : (@IN _110613 x P) = (P x).
Proof. exact (@lem4797235 _110613 P x). Qed.
Lemma lem4797237 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) : (@IN _110613 x s) = (s x).
Proof. exact (@lem4797236 _110613 s x). Qed.
Lemma lem4797238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797239 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) : (term41 _110613 x s) = (term42 _110613 s x).
Proof. exact (MK_COMB (@lem4797238) (@lem4797237 _110613 s x)). Qed.
Lemma lem4797243 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4797244 {_110613 : Type'} (P : _110613 -> Prop) (x : _110613) : (@IN _110613 x P) = (P x).
Proof. exact (@lem4797243 _110613 P x). Qed.
Lemma lem4797245 {_110613 : Type'} (s : _110613 -> Prop) (y : _110613) : (@IN _110613 y s) = (s y).
Proof. exact (@lem4797244 _110613 s y). Qed.
Lemma lem4797246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797247 {_110613 : Type'} (s : _110613 -> Prop) (y : _110613) : (term41 _110613 y s) = (term42 _110613 s y).
Proof. exact (MK_COMB (@lem4797246) (@lem4797245 _110613 s y)). Qed.
Lemma lem4797250 {_110613 : Type'} (x : _110613) (y : _110613) : (term43 _110613 x y) = (term43 _110613 x y).
Proof. exact (eq_refl (term43 _110613 x y)). Qed.
Lemma lem4797251 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term44 _110613 s x y) = (term45 _110613 s x y).
Proof. exact (MK_COMB (@lem4797247 _110613 s y) (@lem4797250 _110613 x y)). Qed.
Lemma lem4797254 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term46 _110613 s x y) = (term47 _110613 s x y).
Proof. exact (MK_COMB (@lem4797239 _110613 s x) (@lem4797251 _110613 s x y)). Qed.
Lemma lem4797257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797258 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term48 _110613 s x y) = (term49 _110613 s x y).
Proof. exact (MK_COMB (@lem4797257) (@lem4797254 _110613 s x y)). Qed.
Lemma lem4797259 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4797260 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term50 _110613 s r x y) = (term51 _110613 s r x y).
Proof. exact (MK_COMB (@lem4797258 _110613 s x y) (@lem4797259 _110613 r x y)). Qed.
Lemma lem4797263 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term52 _110613 s r x) = (term53 _110613 s r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797260 _110613 s r x y)). Qed.
Lemma lem4797264 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797265 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term54 _110613 s r x) = (term55 _110613 s r x).
Proof. exact (MK_COMB (@lem4797264 _110613) (@lem4797263 _110613 s r x)). Qed.
Lemma lem4797270 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term56 _110613 s r) = (term57 _110613 s r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797265 _110613 s r x)). Qed.
Lemma lem4797271 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797272 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term10 _110613 s r) = (term58 _110613 s r).
Proof. exact (MK_COMB (@lem4797271 _110613) (@lem4797270 _110613 s r)). Qed.
Lemma lem4797277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797278 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term12 _110613 s r) = (term59 _110613 s r).
Proof. exact (MK_COMB (@lem4797277) (@lem4797272 _110613 s r)). Qed.
Lemma lem4797286 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4797287 {_110613 : Type'} (P : _110613 -> Prop) (x : _110613) : (@IN _110613 x P) = (P x).
Proof. exact (@lem4797286 _110613 P x). Qed.
Lemma lem4797288 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) : (@IN _110613 x t) = (t x).
Proof. exact (@lem4797287 _110613 t x). Qed.
Lemma lem4797289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797290 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) : (term60 _110613 x t) = (term61 _110613 t x).
Proof. exact (MK_COMB (@lem4797289) (@lem4797288 _110613 t x)). Qed.
Lemma lem4797292 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4797293 {_110613 : Type'} (P : _110613 -> Prop) (x : _110613) : (@IN _110613 x P) = (P x).
Proof. exact (@lem4797292 _110613 P x). Qed.
Lemma lem4797294 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) : (@IN _110613 x s) = (s x).
Proof. exact (@lem4797293 _110613 s x). Qed.
Lemma lem4797295 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (x : _110613) : (term62 _110613 t x s) = (term63 _110613 t s x).
Proof. exact (MK_COMB (@lem4797290 _110613 t x) (@lem4797294 _110613 s x)). Qed.
Lemma lem4797298 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term64 _110613 t s) = (term65 _110613 t s).
Proof. exact (fun_ext (fun x : _110613 => @lem4797295 _110613 t s x)). Qed.
Lemma lem4797299 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797300 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term31 _110613 t s) = (term66 _110613 t s).
Proof. exact (MK_COMB (@lem4797299 _110613) (@lem4797298 _110613 t s)). Qed.
Lemma lem4797305 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term32 _110613 r t s) = (term67 _110613 r t s).
Proof. exact (MK_COMB (@lem4797278 _110613 s r) (@lem4797300 _110613 t s)). Qed.
Lemma lem4797308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797309 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term33 _110613 r t s) = (term68 _110613 r t s).
Proof. exact (MK_COMB (@lem4797308) (@lem4797305 _110613 r t s)). Qed.
Lemma lem4797323 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4797324 {_110613 : Type'} (P : _110613 -> Prop) (x : _110613) : (@IN _110613 x P) = (P x).
Proof. exact (@lem4797323 _110613 P x). Qed.
Lemma lem4797325 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) : (@IN _110613 x t) = (t x).
Proof. exact (@lem4797324 _110613 t x). Qed.
Lemma lem4797326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797327 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) : (term41 _110613 x t) = (term42 _110613 t x).
Proof. exact (MK_COMB (@lem4797326) (@lem4797325 _110613 t x)). Qed.
Lemma lem4797331 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4797332 {_110613 : Type'} (P : _110613 -> Prop) (x : _110613) : (@IN _110613 x P) = (P x).
Proof. exact (@lem4797331 _110613 P x). Qed.
Lemma lem4797333 {_110613 : Type'} (t : _110613 -> Prop) (y : _110613) : (@IN _110613 y t) = (t y).
Proof. exact (@lem4797332 _110613 t y). Qed.
Lemma lem4797334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797335 {_110613 : Type'} (t : _110613 -> Prop) (y : _110613) : (term41 _110613 y t) = (term42 _110613 t y).
Proof. exact (MK_COMB (@lem4797334) (@lem4797333 _110613 t y)). Qed.
Lemma lem4797338 {_110613 : Type'} (x : _110613) (y : _110613) : (term43 _110613 x y) = (term43 _110613 x y).
Proof. exact (eq_refl (term43 _110613 x y)). Qed.
Lemma lem4797339 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) : (term44 _110613 t x y) = (term45 _110613 t x y).
Proof. exact (MK_COMB (@lem4797335 _110613 t y) (@lem4797338 _110613 x y)). Qed.
Lemma lem4797342 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) : (term46 _110613 t x y) = (term47 _110613 t x y).
Proof. exact (MK_COMB (@lem4797327 _110613 t x) (@lem4797339 _110613 t x y)). Qed.
Lemma lem4797345 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797346 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) : (term48 _110613 t x y) = (term49 _110613 t x y).
Proof. exact (MK_COMB (@lem4797345) (@lem4797342 _110613 t x y)). Qed.
Lemma lem4797347 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4797348 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term50 _110613 t r x y) = (term51 _110613 t r x y).
Proof. exact (MK_COMB (@lem4797346 _110613 t x y) (@lem4797347 _110613 r x y)). Qed.
Lemma lem4797351 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term52 _110613 t r x) = (term53 _110613 t r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797348 _110613 t r x y)). Qed.
Lemma lem4797352 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797353 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term54 _110613 t r x) = (term55 _110613 t r x).
Proof. exact (MK_COMB (@lem4797352 _110613) (@lem4797351 _110613 t r x)). Qed.
Lemma lem4797358 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) : (term56 _110613 t r) = (term57 _110613 t r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797353 _110613 t r x)). Qed.
Lemma lem4797359 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797360 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) : (term10 _110613 t r) = (term58 _110613 t r).
Proof. exact (MK_COMB (@lem4797359 _110613) (@lem4797358 _110613 t r)). Qed.
Lemma lem4797365 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (r : type1402 _110613) : (term34 _110613 s t r) = (term69 _110613 s t r).
Proof. exact (MK_COMB (@lem4797309 _110613 r t s) (@lem4797360 _110613 t r)). Qed.
Lemma lem4797368 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term35 _110613 s r) = (term70 _110613 s r).
Proof. exact (fun_ext (fun t : _110613 -> Prop => @lem4797365 _110613 s t r)). Qed.
Lemma lem4797369 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797370 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term36 _110613 s r) = (term71 _110613 s r).
Proof. exact (MK_COMB (@lem4797369 _110613) (@lem4797368 _110613 s r)). Qed.
Lemma lem4797375 {_110613 : Type'} (r : type1402 _110613) : (term37 _110613 r) = (term72 _110613 r).
Proof. exact (fun_ext (fun s : _110613 -> Prop => @lem4797370 _110613 s r)). Qed.
Lemma lem4797376 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797377 {_110613 : Type'} (r : type1402 _110613) : (term38 _110613 r) = (term73 _110613 r).
Proof. exact (MK_COMB (@lem4797376 _110613) (@lem4797375 _110613 r)). Qed.
Lemma lem4797382 {_110613 : Type'} : (term39 _110613) = (term74 _110613).
Proof. exact (fun_ext (fun r : type1402 _110613 => @lem4797377 _110613 r)). Qed.
Lemma lem4797383 {_110613 : Type'} : (@all (_110613 -> _110613 -> Prop)) = (@all (_110613 -> _110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> _110613 -> Prop))). Qed.
Lemma lem4797384 {_110613 : Type'} : (term40 _110613) = (term75 _110613).
Proof. exact (MK_COMB (@lem4797383 _110613) (@lem4797382 _110613)). Qed.
Lemma lem4797389 {_110613 : Type'} : (term75 _110613) = (term40 _110613).
Proof. exact (SYM (@lem4797384 _110613)). Qed.
Lemma lem4797391 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4797392 {_110613 : Type'} : (term75 _110613) = (term77 _110613).
Proof. exact (@lem4797391 (term75 _110613)). Qed.
Lemma lem4797393 {_110613 : Type'} : (term77 _110613) = (term75 _110613).
Proof. exact (SYM (@lem4797392 _110613)). Qed.
Lemma lem4797394 {_110613 : Type'} (h1 : term78 _110613) : term78 _110613.
Proof. exact (h1). Qed.
Lemma lem4797397 {_110613 : Type'} (h1 : term77 _110613) : term77 _110613.
Proof. exact (h1). Qed.
Lemma lem4797398 {_110613 : Type'} : term79 _110613.
Proof. exact (fun h0 : term77 _110613 => @lem4797397 _110613 h0). Qed.
Lemma lem4797399 {_110613 : Type'} (h1 : term79 _110613) : term79 _110613.
Proof. exact (h1). Qed.
Lemma lem4797400 {_110613 : Type'} (h1 : term77 _110613) : term77 _110613.
Proof. exact (h1). Qed.
Lemma lem4797401 {_110613 : Type'} (h1 : term77 _110613) (h2 : term79 _110613) : term77 _110613.
Proof. exact (@lem4797399 _110613 h2 (@lem4797400 _110613 h1)). Qed.
Lemma lem4797402 {_110613 : Type'} (h1 : term77 _110613) : term80 _110613.
Proof. exact (fun h0 : term79 _110613 => @lem4797401 _110613 h1 h0). Qed.
Lemma lem4797403 {_110613 : Type'} (h1 : term79 _110613) : term79 _110613.
Proof. exact (h1). Qed.
Lemma lem4797404 {_110613 : Type'} (h1 : term77 _110613) (h2 : term79 _110613) : term77 _110613.
Proof. exact (@lem4797402 _110613 h1 (@lem4797403 _110613 h2)). Qed.
Lemma lem4797405 {_110613 : Type'} (h1 : term79 _110613) : term79 _110613.
Proof. exact (fun h0 : term77 _110613 => @lem4797404 _110613 h0 h1). Qed.
Lemma lem4797406 {_110613 : Type'} : term81 _110613.
Proof. exact (fun h0 : term79 _110613 => @lem4797405 _110613 h0). Qed.
Lemma lem4797409 {_110613 : Type'} : term79 _110613.
Proof. exact (@lem4797406 _110613 (@lem4797398 _110613)). Qed.
Lemma lem4797410 {_110613 : Type'} : term79 _110613.
Proof. exact (@lem4797409 _110613). Qed.
Lemma lem4797412 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4797413 {_110613 : Type'} : (term77 _110613) = (term82 _110613).
Proof. exact (@lem4797412 (term78 _110613)). Qed.
Lemma lem4797415 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4797416 {_110613 : Type'} : (term82 _110613) = (term75 _110613).
Proof. exact (@lem4797415 (term75 _110613)). Qed.
Lemma lem4797471 {_110613 : Type'} : (term77 _110613) = (term75 _110613).
Proof. exact (TRANS (@lem4797413 _110613) (@lem4797416 _110613)). Qed.
Lemma lem4797486 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term51 _110613 t r x y) = (term51 _110613 t r x y).
Proof. exact (eq_refl (term51 _110613 t r x y)). Qed.
Lemma lem4797487 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term53 _110613 t r x) = (term53 _110613 t r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797486 _110613 t r x y)). Qed.
Lemma lem4797488 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797489 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term55 _110613 t r x) = (term55 _110613 t r x).
Proof. exact (MK_COMB (@lem4797488 _110613) (@lem4797487 _110613 t r x)). Qed.
Lemma lem4797490 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) : (term57 _110613 t r) = (term57 _110613 t r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797489 _110613 t r x)). Qed.
Lemma lem4797491 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797492 {_110613 : Type'} (t : _110613 -> Prop) (r : type1402 _110613) : (term58 _110613 t r) = (term58 _110613 t r).
Proof. exact (MK_COMB (@lem4797491 _110613) (@lem4797490 _110613 t r)). Qed.
Lemma lem4797497 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (x : _110613) : (term63 _110613 t s x) = (term63 _110613 t s x).
Proof. exact (eq_refl (term63 _110613 t s x)). Qed.
Lemma lem4797498 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term65 _110613 t s) = (term65 _110613 t s).
Proof. exact (fun_ext (fun x : _110613 => @lem4797497 _110613 t s x)). Qed.
Lemma lem4797499 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797500 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term66 _110613 t s) = (term66 _110613 t s).
Proof. exact (MK_COMB (@lem4797499 _110613) (@lem4797498 _110613 t s)). Qed.
Lemma lem4797515 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term51 _110613 s r x y) = (term51 _110613 s r x y).
Proof. exact (eq_refl (term51 _110613 s r x y)). Qed.
Lemma lem4797516 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term53 _110613 s r x) = (term53 _110613 s r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797515 _110613 s r x y)). Qed.
Lemma lem4797517 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797518 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term55 _110613 s r x) = (term55 _110613 s r x).
Proof. exact (MK_COMB (@lem4797517 _110613) (@lem4797516 _110613 s r x)). Qed.
Lemma lem4797519 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term57 _110613 s r) = (term57 _110613 s r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797518 _110613 s r x)). Qed.
Lemma lem4797520 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797521 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term58 _110613 s r) = (term58 _110613 s r).
Proof. exact (MK_COMB (@lem4797520 _110613) (@lem4797519 _110613 s r)). Qed.
Lemma lem4797522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797523 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term59 _110613 s r) = (term59 _110613 s r).
Proof. exact (MK_COMB (@lem4797522) (@lem4797521 _110613 s r)). Qed.
Lemma lem4797524 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term67 _110613 r t s) = (term67 _110613 r t s).
Proof. exact (MK_COMB (@lem4797523 _110613 s r) (@lem4797500 _110613 t s)). Qed.
Lemma lem4797525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4797526 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term68 _110613 r t s) = (term68 _110613 r t s).
Proof. exact (MK_COMB (@lem4797525) (@lem4797524 _110613 r t s)). Qed.
Lemma lem4797527 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (r : type1402 _110613) : (term69 _110613 s t r) = (term69 _110613 s t r).
Proof. exact (MK_COMB (@lem4797526 _110613 r t s) (@lem4797492 _110613 t r)). Qed.
Lemma lem4797528 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term70 _110613 s r) = (term70 _110613 s r).
Proof. exact (fun_ext (fun t : _110613 -> Prop => @lem4797527 _110613 s t r)). Qed.
Lemma lem4797529 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797530 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term71 _110613 s r) = (term71 _110613 s r).
Proof. exact (MK_COMB (@lem4797529 _110613) (@lem4797528 _110613 s r)). Qed.
Lemma lem4797531 {_110613 : Type'} (r : type1402 _110613) : (term72 _110613 r) = (term72 _110613 r).
Proof. exact (fun_ext (fun s : _110613 -> Prop => @lem4797530 _110613 s r)). Qed.
Lemma lem4797532 {_110613 : Type'} : (@all (_110613 -> Prop)) = (@all (_110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> Prop))). Qed.
Lemma lem4797533 {_110613 : Type'} (r : type1402 _110613) : (term73 _110613 r) = (term73 _110613 r).
Proof. exact (MK_COMB (@lem4797532 _110613) (@lem4797531 _110613 r)). Qed.
Lemma lem4797534 {_110613 : Type'} : (term74 _110613) = (term74 _110613).
Proof. exact (fun_ext (fun r : type1402 _110613 => @lem4797533 _110613 r)). Qed.
Lemma lem4797535 {_110613 : Type'} : (@all (_110613 -> _110613 -> Prop)) = (@all (_110613 -> _110613 -> Prop)).
Proof. exact (eq_refl (@all (_110613 -> _110613 -> Prop))). Qed.
Lemma lem4797536 {_110613 : Type'} : (term75 _110613) = (term75 _110613).
Proof. exact (MK_COMB (@lem4797535 _110613) (@lem4797534 _110613)). Qed.
Lemma lem4797605 {_110613 : Type'} : (term77 _110613) = (term75 _110613).
Proof. exact (TRANS (@lem4797471 _110613) (@lem4797536 _110613)). Qed.
Lemma lem4797606 {_110613 : Type'} : (term75 _110613) = (term77 _110613).
Proof. exact (SYM (@lem4797605 _110613)). Qed.
Lemma lem4797607 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term67 _110613 r t s.
Proof. exact (h1). Qed.
Lemma lem4797610 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4797611 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) : (r x y) = (term84 _110613 r x y).
Proof. exact (@lem4797610 (r x y)). Qed.
Lemma lem4797612 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) : (term84 _110613 r x y) = (r x y).
Proof. exact (SYM (@lem4797611 _110613 r x y)). Qed.
Lemma lem4797613 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (h1). Qed.
Lemma lem4797618 {_110613 : Type'} (x : _110613) (y : _110613) : (term86 _110613 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4797620 {_110613 : Type'} (s : _110613 -> Prop) (y : _110613) : (term87 _110613 s y) = (term87 _110613 s y).
Proof. exact (eq_refl (term87 _110613 s y)). Qed.
Lemma lem4797621 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term88 _110613 s x y) = (term89 _110613 s x y).
Proof. exact (MK_COMB (@lem4797620 _110613 s y) (@lem4797618 _110613 x y)). Qed.
Lemma lem4797622 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term90 _110613 s x y) = (term88 _110613 s x y).
Proof. exact (@lem17045 (s y) (term43 _110613 x y)). Qed.
Lemma lem4797623 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term90 _110613 s x y) = (term89 _110613 s x y).
Proof. exact (TRANS (@lem4797622 _110613 s x y) (@lem4797621 _110613 s x y)). Qed.
Lemma lem4797625 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) : (term87 _110613 s x) = (term87 _110613 s x).
Proof. exact (eq_refl (term87 _110613 s x)). Qed.
Lemma lem4797626 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term91 _110613 s x y) = (term92 _110613 s x y).
Proof. exact (MK_COMB (@lem4797625 _110613 s x) (@lem4797623 _110613 s x y)). Qed.
Lemma lem4797627 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term93 _110613 s x y) = (term91 _110613 s x y).
Proof. exact (@lem17045 (s x) (term45 _110613 s x y)). Qed.
Lemma lem4797628 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term93 _110613 s x y) = (term92 _110613 s x y).
Proof. exact (TRANS (@lem4797627 _110613 s x y) (@lem4797626 _110613 s x y)). Qed.
Lemma lem4797629 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4797630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4797631 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) (y : _110613) : (term94 _110613 s x y) = (term95 _110613 s x y).
Proof. exact (MK_COMB (@lem4797630) (@lem4797628 _110613 s x y)). Qed.
Lemma lem4797632 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term96 _110613 s r x y) = (term97 _110613 s r x y).
Proof. exact (MK_COMB (@lem4797631 _110613 s x y) (@lem4797629 _110613 r x y)). Qed.
Lemma lem4797633 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term51 _110613 s r x y) = (term96 _110613 s r x y).
Proof. exact (@lem17265 (term47 _110613 s x y) (r x y)). Qed.
Lemma lem4797634 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term51 _110613 s r x y) = (term97 _110613 s r x y).
Proof. exact (TRANS (@lem4797633 _110613 s r x y) (@lem4797632 _110613 s r x y)). Qed.
Lemma lem4797635 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term53 _110613 s r x) = (term98 _110613 s r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797634 _110613 s r x y)). Qed.
Lemma lem4797636 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797637 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term55 _110613 s r x) = (term99 _110613 s r x).
Proof. exact (MK_COMB (@lem4797636 _110613) (@lem4797635 _110613 s r x)). Qed.
Lemma lem4797638 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term57 _110613 s r) = (term100 _110613 s r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797637 _110613 s r x)). Qed.
Lemma lem4797639 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797640 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term58 _110613 s r) = (term101 _110613 s r).
Proof. exact (MK_COMB (@lem4797639 _110613) (@lem4797638 _110613 s r)). Qed.
Lemma lem4797647 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (x : _110613) : (term63 _110613 t s x) = (term102 _110613 t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4797648 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term65 _110613 t s) = (term103 _110613 t s).
Proof. exact (fun_ext (fun x : _110613 => @lem4797647 _110613 t s x)). Qed.
Lemma lem4797649 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797650 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term66 _110613 t s) = (term104 _110613 t s).
Proof. exact (MK_COMB (@lem4797649 _110613) (@lem4797648 _110613 t s)). Qed.
Lemma lem4797651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797652 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term59 _110613 s r) = (term105 _110613 s r).
Proof. exact (MK_COMB (@lem4797651) (@lem4797640 _110613 s r)). Qed.
Lemma lem4797741 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term67 _110613 r t s) = (term106 _110613 r t s).
Proof. exact (MK_COMB (@lem4797652 _110613 s r) (@lem4797650 _110613 t s)). Qed.
Lemma lem4797742 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term106 _110613 r t s.
Proof. exact (EQ_MP (@lem4797741 _110613 r t s) (@lem4797607 _110613 r t s h1)). Qed.
Lemma lem4797756 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term47 _110613 t x y.
Proof. exact (h1). Qed.
Lemma lem4797762 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (h1). Qed.
Lemma lem4797773 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (x : _110613) : (term102 _110613 t s x) = (term102 _110613 t s x).
Proof. exact (eq_refl (term102 _110613 t s x)). Qed.
Lemma lem4797774 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term103 _110613 t s) = (term103 _110613 t s).
Proof. exact (fun_ext (fun x : _110613 => @lem4797773 _110613 t s x)). Qed.
Lemma lem4797775 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797776 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term104 _110613 t s) = (term104 _110613 t s).
Proof. exact (MK_COMB (@lem4797775 _110613) (@lem4797774 _110613 t s)). Qed.
Lemma lem4797805 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term97 _110613 s r x y) = (term97 _110613 s r x y).
Proof. exact (eq_refl (term97 _110613 s r x y)). Qed.
Lemma lem4797806 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term98 _110613 s r x) = (term98 _110613 s r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797805 _110613 s r x y)). Qed.
Lemma lem4797807 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797808 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term99 _110613 s r x) = (term99 _110613 s r x).
Proof. exact (MK_COMB (@lem4797807 _110613) (@lem4797806 _110613 s r x)). Qed.
Lemma lem4797809 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term100 _110613 s r) = (term100 _110613 s r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797808 _110613 s r x)). Qed.
Lemma lem4797810 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797811 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term101 _110613 s r) = (term101 _110613 s r).
Proof. exact (MK_COMB (@lem4797810 _110613) (@lem4797809 _110613 s r)). Qed.
Lemma lem4797812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4797813 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term105 _110613 s r) = (term105 _110613 s r).
Proof. exact (MK_COMB (@lem4797812) (@lem4797811 _110613 s r)). Qed.
Lemma lem4797814 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) : (term106 _110613 r t s) = (term106 _110613 r t s).
Proof. exact (MK_COMB (@lem4797813 _110613 s r) (@lem4797776 _110613 t s)). Qed.
Lemma lem4797815 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term106 _110613 r t s.
Proof. exact (EQ_MP (@lem4797814 _110613 r t s) (@lem4797742 _110613 r t s h1)). Qed.
Lemma lem4797835 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term47 _110613 t x y.
Proof. exact (h1). Qed.
Lemma lem4797843 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (h1). Qed.
Lemma lem4797844 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term45 _110613 t x y.
Proof. exact (proj2 (@lem4797835 _110613 t x y h1)). Qed.
Lemma lem4797848 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term104 _110613 t s.
Proof. exact (proj2 (@lem4797815 _110613 r t s h1)). Qed.
Lemma lem4797849 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term101 _110613 s r.
Proof. exact (proj1 (@lem4797815 _110613 r t s h1)). Qed.
Lemma lem4797853 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (h1). Qed.
Lemma lem4797885 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) (y : _110613) : (term97 _110613 s r x y) = (term97 _110613 s r x y).
Proof. exact (eq_refl (term97 _110613 s r x y)). Qed.
Lemma lem4797886 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term98 _110613 s r x) = (term98 _110613 s r x).
Proof. exact (fun_ext (fun y : _110613 => @lem4797885 _110613 s r x y)). Qed.
Lemma lem4797887 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797888 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (x : _110613) : (term99 _110613 s r x) = (term99 _110613 s r x).
Proof. exact (MK_COMB (@lem4797887 _110613) (@lem4797886 _110613 s r x)). Qed.
Lemma lem4797889 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term100 _110613 s r) = (term100 _110613 s r).
Proof. exact (fun_ext (fun x : _110613 => @lem4797888 _110613 s r x)). Qed.
Lemma lem4797890 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797892 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : (term101 _110613 s r) = (term101 _110613 s r).
Proof. exact (MK_COMB (@lem4797890 _110613) (@lem4797889 _110613 s r)). Qed.
Lemma lem4797893 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term101 _110613 s r.
Proof. exact (EQ_MP (@lem4797892 _110613 s r) (@lem4797849 _110613 r t s h1)). Qed.
Lemma lem4797901 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (x : _110613) : (term102 _110613 t s x) = (term102 _110613 t s x).
Proof. exact (eq_refl (term102 _110613 t s x)). Qed.
Lemma lem4797902 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term103 _110613 t s) = (term103 _110613 t s).
Proof. exact (fun_ext (fun x : _110613 => @lem4797901 _110613 t s x)). Qed.
Lemma lem4797903 {_110613 : Type'} : (@all _110613) = (@all _110613).
Proof. exact (eq_refl (@all _110613)). Qed.
Lemma lem4797905 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) : (term104 _110613 t s) = (term104 _110613 t s).
Proof. exact (MK_COMB (@lem4797903 _110613) (@lem4797902 _110613 t s)). Qed.
Lemma lem4797906 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term104 _110613 t s.
Proof. exact (EQ_MP (@lem4797905 _110613 t s) (@lem4797848 _110613 r t s h1)). Qed.
Lemma lem4797907 {_110613 : Type'} (_59363 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term107 _110613 s r _59363.
Proof. exact (@lem4797893 _110613 r t s h1 _59363). Qed.
Lemma lem4797908 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) : (term107 _110613 s r _59363) = (term99 _110613 s r _59363).
Proof. exact (eq_refl (term107 _110613 s r _59363)). Qed.
Lemma lem4797909 {_110613 : Type'} (_59363 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term99 _110613 s r _59363.
Proof. exact (EQ_MP (@lem4797908 _110613 s r _59363) (@lem4797907 _110613 _59363 r t s h1)). Qed.
Lemma lem4797910 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term108 _110613 s r _59363 _59364.
Proof. exact (@lem4797909 _110613 _59363 r t s h1 _59364). Qed.
Lemma lem4797911 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term108 _110613 s r _59363 _59364) = (term97 _110613 s r _59363 _59364).
Proof. exact (eq_refl (term108 _110613 s r _59363 _59364)). Qed.
Lemma lem4797912 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term97 _110613 s r _59363 _59364.
Proof. exact (EQ_MP (@lem4797911 _110613 s r _59363 _59364) (@lem4797910 _110613 _59363 _59364 r t s h1)). Qed.
Lemma lem4797913 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term109 _110613 t s _59365.
Proof. exact (@lem4797906 _110613 r t s h1 _59365). Qed.
Lemma lem4797914 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (_59365 : _110613) : (term109 _110613 t s _59365) = (term102 _110613 t s _59365).
Proof. exact (eq_refl (term109 _110613 t s _59365)). Qed.
Lemma lem4797917 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (h1). Qed.
Lemma lem4797923 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term43 _110613 x y.
Proof. exact (proj2 (@lem4797844 _110613 t x y h1)). Qed.
Lemma lem4797927 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term97 _110613 s r _59363 _59364) = (term110 _110613 s r _59363 _59364).
Proof. exact (@lem4797017 (term111 _110613 s _59363) (term89 _110613 s _59363 _59364) (r _59363 _59364)). Qed.
Lemma lem4797934 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term112 _110613 s r _59363 _59364) = (term113 _110613 s r _59363 _59364).
Proof. exact (@lem4797017 (term111 _110613 s _59364) (_59363 = _59364) (r _59363 _59364)). Qed.
Lemma lem4797935 {_110613 : Type'} (s : _110613 -> Prop) (_59363 : _110613) : (term87 _110613 s _59363) = (term87 _110613 s _59363).
Proof. exact (eq_refl (term87 _110613 s _59363)). Qed.
Lemma lem4797938 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term110 _110613 s r _59363 _59364) = (term114 _110613 s r _59363 _59364).
Proof. exact (MK_COMB (@lem4797935 _110613 s _59363) (@lem4797934 _110613 s r _59363 _59364)). Qed.
Lemma lem4797940 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term97 _110613 s r _59363 _59364) = (term114 _110613 s r _59363 _59364).
Proof. exact (TRANS (@lem4797927 _110613 s r _59363 _59364) (@lem4797938 _110613 s r _59363 _59364)). Qed.
Lemma lem4797941 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term114 _110613 s r _59363 _59364.
Proof. exact (EQ_MP (@lem4797940 _110613 s r _59363 _59364) (@lem4797912 _110613 _59363 _59364 r t s h1)). Qed.
Lemma lem4797947 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term102 _110613 t s _59365.
Proof. exact (EQ_MP (@lem4797914 _110613 t s _59365) (@lem4797913 _110613 _59365 r t s h1)). Qed.
Lemma lem4797994 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : t x.
Proof. exact (proj1 (@lem4797835 _110613 t x y h1)). Qed.
Lemma lem4797995 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term115 _110613 t x.
Proof. exact (fun h0 : term111 _110613 t x => @lem4797994 _110613 t x y h1). Qed.
Lemma lem4797997 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4797998 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) : (term115 _110613 t x) = (t x).
Proof. exact (@lem4797997 (t x)). Qed.
Lemma lem4797999 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : t x.
Proof. exact (EQ_MP (@lem4797998 _110613 t x) (@lem4797995 _110613 t x y h1)). Qed.
Lemma lem4798005 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4798006 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : (term102 _110613 t s _59365) = (term117 _110613 s t _59365).
Proof. exact (@lem4798005 (s _59365) (term111 _110613 t _59365)). Qed.
Lemma lem4798012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4798013 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : (term118 _110613 t s _59365) = (term119 _110613 s t _59365).
Proof. exact (MK_COMB (@lem4798012) (@lem4798006 _110613 s t _59365)). Qed.
Lemma lem4798019 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : (term117 _110613 s t _59365) = (term117 _110613 s t _59365).
Proof. exact (eq_refl (term117 _110613 s t _59365)). Qed.
Lemma lem4798020 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : ((term102 _110613 t s _59365) = (term117 _110613 s t _59365)) = ((term117 _110613 s t _59365) = (term117 _110613 s t _59365)).
Proof. exact (MK_COMB (@lem4798013 _110613 s t _59365) (@lem4798019 _110613 s t _59365)). Qed.
Lemma lem4798022 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4798023 (x : Prop) : (x = x) = True.
Proof. exact (@lem4798022 Prop x). Qed.
Lemma lem4798024 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : ((term117 _110613 s t _59365) = (term117 _110613 s t _59365)) = True.
Proof. exact (@lem4798023 (term117 _110613 s t _59365)). Qed.
Lemma lem4798025 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : ((term102 _110613 t s _59365) = (term117 _110613 s t _59365)) = True.
Proof. exact (TRANS (@lem4798020 _110613 s t _59365) (@lem4798024 _110613 s t _59365)). Qed.
Lemma lem4798026 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : True = ((term102 _110613 t s _59365) = (term117 _110613 s t _59365)).
Proof. exact (SYM (@lem4798025 _110613 s t _59365)). Qed.
Lemma lem4798027 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (_59365 : _110613) : (term102 _110613 t s _59365) = (term117 _110613 s t _59365).
Proof. exact (EQ_MP (@lem4798026 _110613 s t _59365) (@lem0)). Qed.
Lemma lem4798028 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term117 _110613 s t _59365.
Proof. exact (EQ_MP (@lem4798027 _110613 s t _59365) (@lem4797947 _110613 _59365 r t s h1)). Qed.
Lemma lem4798030 (b : Prop) (a : Prop) : (a \/ b) = (term120 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4798031 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (_59365 : _110613) : (term117 _110613 s t _59365) = (term121 _110613 t s _59365).
Proof. exact (@lem4798030 (term111 _110613 t _59365) (s _59365)). Qed.
Lemma lem4798033 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4798034 {_110613 : Type'} (t : _110613 -> Prop) (_59365 : _110613) : (term122 _110613 t _59365) = (t _59365).
Proof. exact (@lem4798033 (t _59365)). Qed.
Lemma lem4798035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4798036 {_110613 : Type'} (t : _110613 -> Prop) (_59365 : _110613) : (term123 _110613 t _59365) = (term61 _110613 t _59365).
Proof. exact (MK_COMB (@lem4798035) (@lem4798034 _110613 t _59365)). Qed.
Lemma lem4798037 {_110613 : Type'} (s : _110613 -> Prop) (_59365 : _110613) : (s _59365) = (s _59365).
Proof. exact (eq_refl (s _59365)). Qed.
Lemma lem4798038 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (_59365 : _110613) : (term121 _110613 t s _59365) = (term63 _110613 t s _59365).
Proof. exact (MK_COMB (@lem4798036 _110613 t _59365) (@lem4798037 _110613 s _59365)). Qed.
Lemma lem4798039 {_110613 : Type'} (t : _110613 -> Prop) (s : _110613 -> Prop) (_59365 : _110613) : (term117 _110613 s t _59365) = (term63 _110613 t s _59365).
Proof. exact (TRANS (@lem4798031 _110613 t s _59365) (@lem4798038 _110613 t s _59365)). Qed.
Lemma lem4798042 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term63 _110613 t s _59365.
Proof. exact (EQ_MP (@lem4798039 _110613 t s _59365) (@lem4798028 _110613 _59365 r t s h1)). Qed.
Lemma lem4798043 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term63 _110613 t s _59365.
Proof. exact (@lem4798042 _110613 _59365 r t s h1). Qed.
Lemma lem4798044 {_110613 : Type'} (x : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term63 _110613 t s x.
Proof. exact (@lem4798043 _110613 x r t s h1). Qed.
Lemma lem4798047 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : s x.
Proof. exact (@lem4798044 _110613 x r t s h1 (@lem4797999 _110613 t x y h2)). Qed.
Lemma lem4798048 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : term115 _110613 s x.
Proof. exact (fun h0 : term111 _110613 s x => @lem4798047 _110613 r s t x y h1 h2). Qed.
Lemma lem4798050 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4798051 {_110613 : Type'} (s : _110613 -> Prop) (x : _110613) : (term115 _110613 s x) = (s x).
Proof. exact (@lem4798050 (s x)). Qed.
Lemma lem4798052 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : s x.
Proof. exact (EQ_MP (@lem4798051 _110613 s x) (@lem4798048 _110613 r s t x y h1 h2)). Qed.
Lemma lem4798054 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : t y.
Proof. exact (proj1 (@lem4797844 _110613 t x y h1)). Qed.
Lemma lem4798055 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term115 _110613 t y.
Proof. exact (fun h0 : term111 _110613 t y => @lem4798054 _110613 t x y h1). Qed.
Lemma lem4798057 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4798058 {_110613 : Type'} (t : _110613 -> Prop) (y : _110613) : (term115 _110613 t y) = (t y).
Proof. exact (@lem4798057 (t y)). Qed.
Lemma lem4798059 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : t y.
Proof. exact (EQ_MP (@lem4798058 _110613 t y) (@lem4798055 _110613 t x y h1)). Qed.
Lemma lem4798061 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term63 _110613 t s _59365.
Proof. exact (EQ_MP (@lem4798039 _110613 t s _59365) (@lem4798028 _110613 _59365 r t s h1)). Qed.
Lemma lem4798062 {_110613 : Type'} (_59365 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term63 _110613 t s _59365.
Proof. exact (@lem4798061 _110613 _59365 r t s h1). Qed.
Lemma lem4798063 {_110613 : Type'} (y : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term63 _110613 t s y.
Proof. exact (@lem4798062 _110613 y r t s h1). Qed.
Lemma lem4798066 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : s y.
Proof. exact (@lem4798063 _110613 y r t s h1 (@lem4798059 _110613 t x y h2)). Qed.
Lemma lem4798067 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : term115 _110613 s y.
Proof. exact (fun h0 : term111 _110613 s y => @lem4798066 _110613 r s t x y h1 h2). Qed.
Lemma lem4798069 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4798070 {_110613 : Type'} (s : _110613 -> Prop) (y : _110613) : (term115 _110613 s y) = (s y).
Proof. exact (@lem4798069 (s y)). Qed.
Lemma lem4798071 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : s y.
Proof. exact (EQ_MP (@lem4798070 _110613 s y) (@lem4798067 _110613 r s t x y h1 h2)). Qed.
Lemma lem4798073 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (h1). Qed.
Lemma lem4798074 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term124 _110613 r x y.
Proof. exact (fun h0 : r x y => @lem4798073 _110613 r x y h1). Qed.
Lemma lem4798076 (p : Prop) : (term125 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4798077 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) : (term124 _110613 r x y) = (term85 _110613 r x y).
Proof. exact (@lem4798076 (r x y)). Qed.
Lemma lem4798078 {_110613 : Type'} (r : type1402 _110613) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) : term85 _110613 r x y.
Proof. exact (EQ_MP (@lem4798077 _110613 r x y) (@lem4798074 _110613 r x y h1)). Qed.
Lemma lem4798094 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4798095 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term113 _110613 s r _59363 _59364) = (term126 _110613 s r _59363 _59364).
Proof. exact (@lem4798094 (_59363 = _59364) (term111 _110613 s _59364) (r _59363 _59364)). Qed.
Lemma lem4798111 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4798112 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term127 _110613 s r _59363 _59364) = (term128 _110613 r _59363 s _59364).
Proof. exact (@lem4798111 (r _59363 _59364) (term111 _110613 s _59364)). Qed.
Lemma lem4798118 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) : (term129 _110613 _59363 _59364) = (term129 _110613 _59363 _59364).
Proof. exact (eq_refl (term129 _110613 _59363 _59364)). Qed.
Lemma lem4798119 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term126 _110613 s r _59363 _59364) = (term130 _110613 r _59363 s _59364).
Proof. exact (MK_COMB (@lem4798118 _110613 _59363 _59364) (@lem4798112 _110613 r _59363 s _59364)). Qed.
Lemma lem4798123 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4798124 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term130 _110613 r _59363 s _59364) = (term131 _110613 r _59363 s _59364).
Proof. exact (@lem4798123 (r _59363 _59364) (_59363 = _59364) (term111 _110613 s _59364)). Qed.
Lemma lem4798142 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term126 _110613 s r _59363 _59364) = (term131 _110613 r _59363 s _59364).
Proof. exact (TRANS (@lem4798119 _110613 r _59363 s _59364) (@lem4798124 _110613 r _59363 s _59364)). Qed.
Lemma lem4798143 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term113 _110613 s r _59363 _59364) = (term131 _110613 r _59363 s _59364).
Proof. exact (TRANS (@lem4798095 _110613 s r _59363 _59364) (@lem4798142 _110613 r _59363 s _59364)). Qed.
Lemma lem4798144 {_110613 : Type'} (s : _110613 -> Prop) (_59363 : _110613) : (term87 _110613 s _59363) = (term87 _110613 s _59363).
Proof. exact (eq_refl (term87 _110613 s _59363)). Qed.
Lemma lem4798145 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term114 _110613 s r _59363 _59364) = (term132 _110613 r _59363 s _59364).
Proof. exact (MK_COMB (@lem4798144 _110613 s _59363) (@lem4798143 _110613 r _59363 s _59364)). Qed.
Lemma lem4798149 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4798150 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term132 _110613 r _59363 s _59364) = (term133 _110613 r _59363 s _59364).
Proof. exact (@lem4798149 (r _59363 _59364) (term111 _110613 s _59363) (term134 _110613 _59363 s _59364)). Qed.
Lemma lem4798164 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4798165 {_110613 : Type'} (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term135 _110613 _59363 s _59364) = (term136 _110613 _59363 s _59364).
Proof. exact (@lem4798164 (_59363 = _59364) (term111 _110613 s _59363) (term111 _110613 s _59364)). Qed.
Lemma lem4798183 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term137 _110613 r _59363 _59364) = (term137 _110613 r _59363 _59364).
Proof. exact (eq_refl (term137 _110613 r _59363 _59364)). Qed.
Lemma lem4798184 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term133 _110613 r _59363 s _59364) = (term138 _110613 r _59363 s _59364).
Proof. exact (MK_COMB (@lem4798183 _110613 r _59363 _59364) (@lem4798165 _110613 _59363 s _59364)). Qed.
Lemma lem4798195 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term132 _110613 r _59363 s _59364) = (term138 _110613 r _59363 s _59364).
Proof. exact (TRANS (@lem4798150 _110613 r _59363 s _59364) (@lem4798184 _110613 r _59363 s _59364)). Qed.
Lemma lem4798196 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term114 _110613 s r _59363 _59364) = (term138 _110613 r _59363 s _59364).
Proof. exact (TRANS (@lem4798145 _110613 r _59363 s _59364) (@lem4798195 _110613 r _59363 s _59364)). Qed.
Lemma lem4798197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4798198 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term139 _110613 s r _59363 _59364) = (term140 _110613 r _59363 s _59364).
Proof. exact (MK_COMB (@lem4798197) (@lem4798196 _110613 r _59363 s _59364)). Qed.
Lemma lem4798224 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4798225 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term127 _110613 s r _59363 _59364) = (term128 _110613 r _59363 s _59364).
Proof. exact (@lem4798224 (r _59363 _59364) (term111 _110613 s _59364)). Qed.
Lemma lem4798231 {_110613 : Type'} (s : _110613 -> Prop) (_59363 : _110613) : (term87 _110613 s _59363) = (term87 _110613 s _59363).
Proof. exact (eq_refl (term87 _110613 s _59363)). Qed.
Lemma lem4798232 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term141 _110613 s r _59363 _59364) = (term142 _110613 r _59363 s _59364).
Proof. exact (MK_COMB (@lem4798231 _110613 s _59363) (@lem4798225 _110613 r _59363 s _59364)). Qed.
Lemma lem4798236 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4798237 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term142 _110613 r _59363 s _59364) = (term143 _110613 r _59363 s _59364).
Proof. exact (@lem4798236 (r _59363 _59364) (term111 _110613 s _59363) (term111 _110613 s _59364)). Qed.
Lemma lem4798253 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term141 _110613 s r _59363 _59364) = (term143 _110613 r _59363 s _59364).
Proof. exact (TRANS (@lem4798232 _110613 r _59363 s _59364) (@lem4798237 _110613 r _59363 s _59364)). Qed.
Lemma lem4798254 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) : (term129 _110613 _59363 _59364) = (term129 _110613 _59363 _59364).
Proof. exact (eq_refl (term129 _110613 _59363 _59364)). Qed.
Lemma lem4798255 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term144 _110613 s r _59363 _59364) = (term145 _110613 r _59363 s _59364).
Proof. exact (MK_COMB (@lem4798254 _110613 _59363 _59364) (@lem4798253 _110613 r _59363 s _59364)). Qed.
Lemma lem4798259 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4798260 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term145 _110613 r _59363 s _59364) = (term138 _110613 r _59363 s _59364).
Proof. exact (@lem4798259 (r _59363 _59364) (_59363 = _59364) (term146 _110613 _59363 s _59364)). Qed.
Lemma lem4798288 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : (term144 _110613 s r _59363 _59364) = (term138 _110613 r _59363 s _59364).
Proof. exact (TRANS (@lem4798255 _110613 r _59363 s _59364) (@lem4798260 _110613 r _59363 s _59364)). Qed.
Lemma lem4798289 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : ((term114 _110613 s r _59363 _59364) = (term144 _110613 s r _59363 _59364)) = ((term138 _110613 r _59363 s _59364) = (term138 _110613 r _59363 s _59364)).
Proof. exact (MK_COMB (@lem4798198 _110613 r _59363 s _59364) (@lem4798288 _110613 r _59363 s _59364)). Qed.
Lemma lem4798291 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4798292 (x : Prop) : (x = x) = True.
Proof. exact (@lem4798291 Prop x). Qed.
Lemma lem4798293 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (s : _110613 -> Prop) (_59364 : _110613) : ((term138 _110613 r _59363 s _59364) = (term138 _110613 r _59363 s _59364)) = True.
Proof. exact (@lem4798292 (term138 _110613 r _59363 s _59364)). Qed.
Lemma lem4798294 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : ((term114 _110613 s r _59363 _59364) = (term144 _110613 s r _59363 _59364)) = True.
Proof. exact (TRANS (@lem4798289 _110613 r _59363 s _59364) (@lem4798293 _110613 r _59363 s _59364)). Qed.
Lemma lem4798295 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : True = ((term114 _110613 s r _59363 _59364) = (term144 _110613 s r _59363 _59364)).
Proof. exact (SYM (@lem4798294 _110613 s r _59363 _59364)). Qed.
Lemma lem4798296 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term114 _110613 s r _59363 _59364) = (term144 _110613 s r _59363 _59364).
Proof. exact (EQ_MP (@lem4798295 _110613 s r _59363 _59364) (@lem0)). Qed.
Lemma lem4798297 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term144 _110613 s r _59363 _59364.
Proof. exact (EQ_MP (@lem4798296 _110613 s r _59363 _59364) (@lem4797941 _110613 _59363 _59364 r t s h1)). Qed.
Lemma lem4798299 (b : Prop) (a : Prop) : (a \/ b) = (term120 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4798300 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term144 _110613 s r _59363 _59364) = (term147 _110613 s r _59363 _59364).
Proof. exact (@lem4798299 (term141 _110613 s r _59363 _59364) (_59363 = _59364)). Qed.
Lemma lem4798302 (a : Prop) (b : Prop) : (term148 a b) = (term149 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4798303 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term150 _110613 s r _59363 _59364) = (term151 _110613 s r _59363 _59364).
Proof. exact (@lem4798302 (term111 _110613 s _59363) (term127 _110613 s r _59363 _59364)). Qed.
Lemma lem4798305 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4798306 {_110613 : Type'} (s : _110613 -> Prop) (_59363 : _110613) : (term122 _110613 s _59363) = (s _59363).
Proof. exact (@lem4798305 (s _59363)). Qed.
Lemma lem4798307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798308 {_110613 : Type'} (s : _110613 -> Prop) (_59363 : _110613) : (term152 _110613 s _59363) = (term42 _110613 s _59363).
Proof. exact (MK_COMB (@lem4798307) (@lem4798306 _110613 s _59363)). Qed.
Lemma lem4798310 (a : Prop) (b : Prop) : (term148 a b) = (term149 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4798311 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term153 _110613 s r _59363 _59364) = (term154 _110613 s r _59363 _59364).
Proof. exact (@lem4798310 (term111 _110613 s _59364) (r _59363 _59364)). Qed.
Lemma lem4798313 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4798314 {_110613 : Type'} (s : _110613 -> Prop) (_59364 : _110613) : (term122 _110613 s _59364) = (s _59364).
Proof. exact (@lem4798313 (s _59364)). Qed.
Lemma lem4798315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4798316 {_110613 : Type'} (s : _110613 -> Prop) (_59364 : _110613) : (term152 _110613 s _59364) = (term42 _110613 s _59364).
Proof. exact (MK_COMB (@lem4798315) (@lem4798314 _110613 s _59364)). Qed.
Lemma lem4798317 {_110613 : Type'} (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term85 _110613 r _59363 _59364) = (term85 _110613 r _59363 _59364).
Proof. exact (eq_refl (term85 _110613 r _59363 _59364)). Qed.
Lemma lem4798318 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term154 _110613 s r _59363 _59364) = (term155 _110613 s r _59363 _59364).
Proof. exact (MK_COMB (@lem4798316 _110613 s _59364) (@lem4798317 _110613 r _59363 _59364)). Qed.
Lemma lem4798319 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term153 _110613 s r _59363 _59364) = (term155 _110613 s r _59363 _59364).
Proof. exact (TRANS (@lem4798311 _110613 s r _59363 _59364) (@lem4798318 _110613 s r _59363 _59364)). Qed.
Lemma lem4798320 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term151 _110613 s r _59363 _59364) = (term156 _110613 s r _59363 _59364).
Proof. exact (MK_COMB (@lem4798308 _110613 s _59363) (@lem4798319 _110613 s r _59363 _59364)). Qed.
Lemma lem4798321 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term150 _110613 s r _59363 _59364) = (term156 _110613 s r _59363 _59364).
Proof. exact (TRANS (@lem4798303 _110613 s r _59363 _59364) (@lem4798320 _110613 s r _59363 _59364)). Qed.
Lemma lem4798322 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4798323 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term157 _110613 s r _59363 _59364) = (term158 _110613 s r _59363 _59364).
Proof. exact (MK_COMB (@lem4798322) (@lem4798321 _110613 s r _59363 _59364)). Qed.
Lemma lem4798324 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) : (_59363 = _59364) = (_59363 = _59364).
Proof. exact (eq_refl (_59363 = _59364)). Qed.
Lemma lem4798325 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term147 _110613 s r _59363 _59364) = (term159 _110613 s r _59363 _59364).
Proof. exact (MK_COMB (@lem4798323 _110613 s r _59363 _59364) (@lem4798324 _110613 _59363 _59364)). Qed.
Lemma lem4798326 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) (_59363 : _110613) (_59364 : _110613) : (term144 _110613 s r _59363 _59364) = (term159 _110613 s r _59363 _59364).
Proof. exact (TRANS (@lem4798300 _110613 s r _59363 _59364) (@lem4798325 _110613 s r _59363 _59364)). Qed.
Lemma lem4798328 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : term155 _110613 s r x y.
Proof. exact (conj (@lem4798071 _110613 r s t x y h2 h3) (@lem4798078 _110613 r x y h1)). Qed.
Lemma lem4798329 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : term156 _110613 s r x y.
Proof. exact (conj (@lem4798052 _110613 r s t x y h2 h3) (@lem4798328 _110613 r s t x y h1 h2 h3)). Qed.
Lemma lem4798331 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term159 _110613 s r _59363 _59364.
Proof. exact (EQ_MP (@lem4798326 _110613 s r _59363 _59364) (@lem4798297 _110613 _59363 _59364 r t s h1)). Qed.
Lemma lem4798332 {_110613 : Type'} (_59363 : _110613) (_59364 : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term159 _110613 s r _59363 _59364.
Proof. exact (@lem4798331 _110613 _59363 _59364 r t s h1). Qed.
Lemma lem4798333 {_110613 : Type'} (x : _110613) (y : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term159 _110613 s r x y.
Proof. exact (@lem4798332 _110613 x y r t s h1). Qed.
Lemma lem4798336 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : x = y.
Proof. exact (@lem4798333 _110613 x y r t s h2 (@lem4798329 _110613 r s t x y h1 h2 h3)). Qed.
Lemma lem4798337 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : term160 _110613 x y.
Proof. exact (fun h0 : term43 _110613 x y => @lem4798336 _110613 r s t x y h1 h2 h3). Qed.
Lemma lem4798339 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4798340 {_110613 : Type'} (x : _110613) (y : _110613) : (term160 _110613 x y) = (x = y).
Proof. exact (@lem4798339 (x = y)). Qed.
Lemma lem4798341 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : x = y.
Proof. exact (EQ_MP (@lem4798340 _110613 x y) (@lem4798337 _110613 r s t x y h1 h2 h3)). Qed.
Lemma lem4798344 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4798346 {_110613 : Type'} (x : _110613) (y : _110613) : (term43 _110613 x y) = (term161 _110613 x y).
Proof. exact (@lem4798344 (x = y)). Qed.
Lemma lem4798349 {_110613 : Type'} (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term47 _110613 t x y) : term161 _110613 x y.
Proof. exact (EQ_MP (@lem4798346 _110613 x y) (@lem4797923 _110613 t x y h1)). Qed.
Lemma lem4798352 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (@lem4798349 _110613 t x y h3 (@lem4798341 _110613 r s t x y h1 h2 h3)). Qed.
Lemma lem4798353 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : term162.
Proof. exact (fun h0 : ~ False => @lem4798352 _110613 r s t x y h1 h2 h3). Qed.
Lemma lem4798355 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4798356 : term162 = False.
Proof. exact (@lem4798355 False). Qed.
Lemma lem4798357 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798356) (@lem4798353 _110613 r s t x y h1 h2 h3)). Qed.
Lemma lem4798358 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term85 _110613 r x y) = False.
Proof. exact (prop_ext (fun h4 : term85 _110613 r x y => @lem4798357 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797917 _110613 r x y h1)). Qed.
Lemma lem4798359 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798358 _110613 r s t x y h1 h2 h3) (@lem4797917 _110613 r x y h1)). Qed.
Lemma lem4798360 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term85 _110613 r x y) = False.
Proof. exact (prop_ext (fun h4 : term85 _110613 r x y => @lem4798359 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797853 _110613 r x y h1)). Qed.
Lemma lem4798361 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798360 _110613 r s t x y h1 h2 h3) (@lem4797853 _110613 r x y h1)). Qed.
Lemma lem4798362 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term85 _110613 r x y) = False.
Proof. exact (prop_ext (fun h4 : term85 _110613 r x y => @lem4798361 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797853 _110613 r x y h1)). Qed.
Lemma lem4798363 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798362 _110613 r s t x y h1 h2 h3) (@lem4797853 _110613 r x y h1)). Qed.
Lemma lem4798364 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term85 _110613 r x y) = False.
Proof. exact (prop_ext (fun h4 : term85 _110613 r x y => @lem4798363 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797843 _110613 r x y h1)). Qed.
Lemma lem4798365 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798364 _110613 r s t x y h1 h2 h3) (@lem4797843 _110613 r x y h1)). Qed.
Lemma lem4798366 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term47 _110613 t x y) = False.
Proof. exact (prop_ext (fun h4 : term47 _110613 t x y => @lem4798365 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797835 _110613 t x y h3)). Qed.
Lemma lem4798367 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798366 _110613 r s t x y h1 h2 h3) (@lem4797835 _110613 t x y h3)). Qed.
Lemma lem4798368 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term85 _110613 r x y) = False.
Proof. exact (prop_ext (fun h4 : term85 _110613 r x y => @lem4798367 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797762 _110613 r x y h1)). Qed.
Lemma lem4798369 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798368 _110613 r s t x y h1 h2 h3) (@lem4797762 _110613 r x y h1)). Qed.
Lemma lem4798370 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term47 _110613 t x y) = False.
Proof. exact (prop_ext (fun h4 : term47 _110613 t x y => @lem4798369 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797756 _110613 t x y h3)). Qed.
Lemma lem4798371 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798370 _110613 r s t x y h1 h2 h3) (@lem4797756 _110613 t x y h3)). Qed.
Lemma lem4798372 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : (term85 _110613 r x y) = False.
Proof. exact (prop_ext (fun h4 : term85 _110613 r x y => @lem4798371 _110613 r s t x y h1 h2 h3) (fun h4 : False => @lem4797613 _110613 r x y h1)). Qed.
Lemma lem4798373 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term85 _110613 r x y) (h2 : term67 _110613 r t s) (h3 : term47 _110613 t x y) : False.
Proof. exact (EQ_MP (@lem4798372 _110613 r s t x y h1 h2 h3) (@lem4797613 _110613 r x y h1)). Qed.
Lemma lem4798374 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : term84 _110613 r x y.
Proof. exact (fun h0 : term85 _110613 r x y => @lem4798373 _110613 r s t x y h0 h1 h2). Qed.
Lemma lem4798375 {_110613 : Type'} (r : type1402 _110613) (s : _110613 -> Prop) (t : _110613 -> Prop) (x : _110613) (y : _110613) (h1 : term67 _110613 r t s) (h2 : term47 _110613 t x y) : r x y.
Proof. exact (EQ_MP (@lem4797612 _110613 r x y) (@lem4798374 _110613 r s t x y h1 h2)). Qed.
Lemma lem4798376 {_110613 : Type'} (x : _110613) (y : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term51 _110613 t r x y.
Proof. exact (fun h0 : term47 _110613 t x y => @lem4798375 _110613 r s t x y h1 h0). Qed.
Lemma lem4798381 {_110613 : Type'} (x : _110613) (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term55 _110613 t r x.
Proof. exact (fun y : _110613 => @lem4798376 _110613 x y r t s h1). Qed.
Lemma lem4798386 {_110613 : Type'} (r : type1402 _110613) (t : _110613 -> Prop) (s : _110613 -> Prop) (h1 : term67 _110613 r t s) : term58 _110613 t r.
Proof. exact (fun x : _110613 => @lem4798381 _110613 x r t s h1). Qed.
Lemma lem4798387 {_110613 : Type'} (s : _110613 -> Prop) (t : _110613 -> Prop) (r : type1402 _110613) : term69 _110613 s t r.
Proof. exact (fun h0 : term67 _110613 r t s => @lem4798386 _110613 r t s h0). Qed.
Lemma lem4798392 {_110613 : Type'} (s : _110613 -> Prop) (r : type1402 _110613) : term71 _110613 s r.
Proof. exact (fun t : _110613 -> Prop => @lem4798387 _110613 s t r). Qed.
Lemma lem4798397 {_110613 : Type'} (r : type1402 _110613) : term73 _110613 r.
Proof. exact (fun s : _110613 -> Prop => @lem4798392 _110613 s r). Qed.
Lemma lem4798402 {_110613 : Type'} : term75 _110613.
Proof. exact (fun r : type1402 _110613 => @lem4798397 _110613 r). Qed.
Lemma lem4798403 {_110613 : Type'} : term77 _110613.
Proof. exact (EQ_MP (@lem4797606 _110613) (@lem4798402 _110613)). Qed.
Lemma lem4798405 {_110613 : Type'} : term77 _110613.
Proof. exact (@lem4797410 _110613 (@lem4798403 _110613)). Qed.
Lemma lem4798406 {_110613 : Type'} (h1 : term78 _110613) : False.
Proof. exact (@lem4798405 _110613 (@lem4797394 _110613 h1)). Qed.
Lemma lem4798407 {_110613 : Type'} (h1 : term78 _110613) : (term78 _110613) = False.
Proof. exact (prop_ext (fun h2 : term78 _110613 => @lem4798406 _110613 h1) (fun h2 : False => @lem4797394 _110613 h1)). Qed.
Lemma lem4798408 {_110613 : Type'} (h1 : term78 _110613) : False.
Proof. exact (EQ_MP (@lem4798407 _110613 h1) (@lem4797394 _110613 h1)). Qed.
Lemma lem4798409 {_110613 : Type'} : term77 _110613.
Proof. exact (fun h0 : term78 _110613 => @lem4798408 _110613 h0). Qed.
Lemma lem4798410 {_110613 : Type'} : term75 _110613.
Proof. exact (EQ_MP (@lem4797393 _110613) (@lem4798409 _110613)). Qed.
Lemma lem4798411 {_110613 : Type'} : term40 _110613.
Proof. exact (EQ_MP (@lem4797389 _110613) (@lem4798410 _110613)). Qed.
Lemma lem4798412 {_110613 : Type'} : term30 _110613.
Proof. exact (EQ_MP (@lem4797205 _110613) (@lem4798411 _110613)). Qed.
Lemma lem4798413 {_110613 : Type'} : term29 _110613.
Proof. exact (EQ_MP (@lem4797111 _110613) (@lem4798412 _110613)). Qed.
