Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_ACI_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3291166 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3291167 {_86360 : Type'} (s : _86360 -> Prop) (t : _86360 -> Prop) : (s = t) = (term0 _86360 s t).
Proof. exact (@lem3291166 _86360 s t). Qed.
Lemma lem3291168 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : ((@INTER _86360 p q) = (@INTER _86360 q p)) = (term1 _86360 q p).
Proof. exact (@lem3291167 _86360 (@INTER _86360 p q) (@INTER _86360 q p)). Qed.
Lemma lem3291177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291178 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term2 _86360 q p) = (term3 _86360 q p).
Proof. exact (MK_COMB (@lem3291177) (@lem3291168 _86360 q p)). Qed.
Lemma lem3291184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3291185 {_86360 : Type'} (s : _86360 -> Prop) (t : _86360 -> Prop) : (s = t) = (term0 _86360 s t).
Proof. exact (@lem3291184 _86360 s t). Qed.
Lemma lem3291186 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : ((term4 _86360 p q r) = (term5 _86360 p q r)) = (term6 _86360 p q r).
Proof. exact (@lem3291185 _86360 (term4 _86360 p q r) (term5 _86360 p q r)). Qed.
Lemma lem3291195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291196 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term7 _86360 p q r) = (term8 _86360 p q r).
Proof. exact (MK_COMB (@lem3291195) (@lem3291186 _86360 p q r)). Qed.
Lemma lem3291202 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3291203 {_86360 : Type'} (s : _86360 -> Prop) (t : _86360 -> Prop) : (s = t) = (term0 _86360 s t).
Proof. exact (@lem3291202 _86360 s t). Qed.
Lemma lem3291204 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : ((term5 _86360 p q r) = (term5 _86360 q p r)) = (term9 _86360 q p r).
Proof. exact (@lem3291203 _86360 (term5 _86360 p q r) (term5 _86360 q p r)). Qed.
Lemma lem3291213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291214 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term10 _86360 q p r) = (term11 _86360 q p r).
Proof. exact (MK_COMB (@lem3291213) (@lem3291204 _86360 q p r)). Qed.
Lemma lem3291220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3291221 {_86360 : Type'} (s : _86360 -> Prop) (t : _86360 -> Prop) : (s = t) = (term0 _86360 s t).
Proof. exact (@lem3291220 _86360 s t). Qed.
Lemma lem3291222 {_86360 : Type'} (p : _86360 -> Prop) : ((@INTER _86360 p p) = p) = (term12 _86360 p).
Proof. exact (@lem3291221 _86360 (@INTER _86360 p p) p). Qed.
Lemma lem3291231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291232 {_86360 : Type'} (p : _86360 -> Prop) : (term13 _86360 p) = (term14 _86360 p).
Proof. exact (MK_COMB (@lem3291231) (@lem3291222 _86360 p)). Qed.
Lemma lem3291236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3291237 {_86360 : Type'} (s : _86360 -> Prop) (t : _86360 -> Prop) : (s = t) = (term0 _86360 s t).
Proof. exact (@lem3291236 _86360 s t). Qed.
Lemma lem3291238 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term15 _86360 p q) = (@INTER _86360 p q)) = (term16 _86360 p q).
Proof. exact (@lem3291237 _86360 (term15 _86360 p q) (@INTER _86360 p q)). Qed.
Lemma lem3291247 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term17 _86360 p q) = (term18 _86360 p q).
Proof. exact (MK_COMB (@lem3291232 _86360 p) (@lem3291238 _86360 p q)). Qed.
Lemma lem3291250 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term19 _86360 r p q) = (term20 _86360 r p q).
Proof. exact (MK_COMB (@lem3291214 _86360 q p r) (@lem3291247 _86360 p q)). Qed.
Lemma lem3291253 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term21 _86360 r p q) = (term22 _86360 r p q).
Proof. exact (MK_COMB (@lem3291196 _86360 p q r) (@lem3291250 _86360 r p q)). Qed.
Lemma lem3291256 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term23 _86360 r p q) = (term24 _86360 r p q).
Proof. exact (MK_COMB (@lem3291178 _86360 q p) (@lem3291253 _86360 r p q)). Qed.
Lemma lem3291259 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term24 _86360 r p q) = (term23 _86360 r p q).
Proof. exact (SYM (@lem3291256 _86360 r p q)). Qed.
Lemma lem3291269 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291270 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291269 _86360 s x t). Qed.
Lemma lem3291271 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (q : _86360 -> Prop) : (term25 _86360 x p q) = (term26 _86360 p x q).
Proof. exact (@lem3291270 _86360 p x q). Qed.
Lemma lem3291275 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291276 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291275 _86360 P x). Qed.
Lemma lem3291277 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291276 _86360 p x). Qed.
Lemma lem3291278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291279 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291278) (@lem3291277 _86360 p x)). Qed.
Lemma lem3291281 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291282 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291281 _86360 P x). Qed.
Lemma lem3291283 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291282 _86360 q x). Qed.
Lemma lem3291284 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term26 _86360 p x q) = (term29 _86360 p q x).
Proof. exact (MK_COMB (@lem3291279 _86360 p x) (@lem3291283 _86360 q x)). Qed.
Lemma lem3291287 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term25 _86360 x p q) = (term29 _86360 p q x).
Proof. exact (TRANS (@lem3291271 _86360 p x q) (@lem3291284 _86360 p q x)). Qed.
Lemma lem3291288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291289 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term30 _86360 x p q) = (term31 _86360 p q x).
Proof. exact (MK_COMB (@lem3291288) (@lem3291287 _86360 p q x)). Qed.
Lemma lem3291291 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291292 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291291 _86360 s x t). Qed.
Lemma lem3291293 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (p : _86360 -> Prop) : (term25 _86360 x q p) = (term26 _86360 q x p).
Proof. exact (@lem3291292 _86360 q x p). Qed.
Lemma lem3291297 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291298 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291297 _86360 P x). Qed.
Lemma lem3291299 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291298 _86360 q x). Qed.
Lemma lem3291300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291301 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term27 _86360 x q) = (term28 _86360 q x).
Proof. exact (MK_COMB (@lem3291300) (@lem3291299 _86360 q x)). Qed.
Lemma lem3291303 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291304 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291303 _86360 P x). Qed.
Lemma lem3291305 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291304 _86360 p x). Qed.
Lemma lem3291306 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term26 _86360 q x p) = (term29 _86360 q p x).
Proof. exact (MK_COMB (@lem3291301 _86360 q x) (@lem3291305 _86360 p x)). Qed.
Lemma lem3291309 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term25 _86360 x q p) = (term29 _86360 q p x).
Proof. exact (TRANS (@lem3291293 _86360 q x p) (@lem3291306 _86360 q p x)). Qed.
Lemma lem3291310 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : ((term25 _86360 x p q) = (term25 _86360 x q p)) = ((term29 _86360 p q x) = (term29 _86360 q p x)).
Proof. exact (MK_COMB (@lem3291289 _86360 p q x) (@lem3291309 _86360 q p x)). Qed.
Lemma lem3291313 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term32 _86360 q p) = (term33 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3291310 _86360 q p x)). Qed.
Lemma lem3291314 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3291315 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term1 _86360 q p) = (term34 _86360 q p).
Proof. exact (MK_COMB (@lem3291314 _86360) (@lem3291313 _86360 q p)). Qed.
Lemma lem3291320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291321 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term3 _86360 q p) = (term35 _86360 q p).
Proof. exact (MK_COMB (@lem3291320) (@lem3291315 _86360 q p)). Qed.
Lemma lem3291331 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291332 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291331 _86360 s x t). Qed.
Lemma lem3291333 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) (r : _86360 -> Prop) : (term36 _86360 x p q r) = (term37 _86360 p q x r).
Proof. exact (@lem3291332 _86360 (@INTER _86360 p q) x r). Qed.
Lemma lem3291337 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291338 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291337 _86360 s x t). Qed.
Lemma lem3291339 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (q : _86360 -> Prop) : (term25 _86360 x p q) = (term26 _86360 p x q).
Proof. exact (@lem3291338 _86360 p x q). Qed.
Lemma lem3291343 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291344 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291343 _86360 P x). Qed.
Lemma lem3291345 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291344 _86360 p x). Qed.
Lemma lem3291346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291347 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291346) (@lem3291345 _86360 p x)). Qed.
Lemma lem3291349 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291350 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291349 _86360 P x). Qed.
Lemma lem3291351 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291350 _86360 q x). Qed.
Lemma lem3291352 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term26 _86360 p x q) = (term29 _86360 p q x).
Proof. exact (MK_COMB (@lem3291347 _86360 p x) (@lem3291351 _86360 q x)). Qed.
Lemma lem3291355 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term25 _86360 x p q) = (term29 _86360 p q x).
Proof. exact (TRANS (@lem3291339 _86360 p x q) (@lem3291352 _86360 p q x)). Qed.
Lemma lem3291356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291357 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term38 _86360 x p q) = (term39 _86360 p q x).
Proof. exact (MK_COMB (@lem3291356) (@lem3291355 _86360 p q x)). Qed.
Lemma lem3291359 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291360 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291359 _86360 P x). Qed.
Lemma lem3291361 {_86360 : Type'} (r : _86360 -> Prop) (x : _86360) : (@IN _86360 x r) = (r x).
Proof. exact (@lem3291360 _86360 r x). Qed.
Lemma lem3291362 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term37 _86360 p q x r) = (term40 _86360 p q r x).
Proof. exact (MK_COMB (@lem3291357 _86360 p q x) (@lem3291361 _86360 r x)). Qed.
Lemma lem3291365 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term36 _86360 x p q r) = (term40 _86360 p q r x).
Proof. exact (TRANS (@lem3291333 _86360 p q x r) (@lem3291362 _86360 p q r x)). Qed.
Lemma lem3291366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291367 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term41 _86360 x p q r) = (term42 _86360 p q r x).
Proof. exact (MK_COMB (@lem3291366) (@lem3291365 _86360 p q r x)). Qed.
Lemma lem3291369 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291370 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291369 _86360 s x t). Qed.
Lemma lem3291371 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term43 _86360 x p q r) = (term44 _86360 p x q r).
Proof. exact (@lem3291370 _86360 p x (@INTER _86360 q r)). Qed.
Lemma lem3291375 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291376 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291375 _86360 P x). Qed.
Lemma lem3291377 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291376 _86360 p x). Qed.
Lemma lem3291378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291379 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291378) (@lem3291377 _86360 p x)). Qed.
Lemma lem3291381 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291382 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291381 _86360 s x t). Qed.
Lemma lem3291383 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (r : _86360 -> Prop) : (term25 _86360 x q r) = (term26 _86360 q x r).
Proof. exact (@lem3291382 _86360 q x r). Qed.
Lemma lem3291387 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291388 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291387 _86360 P x). Qed.
Lemma lem3291389 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291388 _86360 q x). Qed.
Lemma lem3291390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291391 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term27 _86360 x q) = (term28 _86360 q x).
Proof. exact (MK_COMB (@lem3291390) (@lem3291389 _86360 q x)). Qed.
Lemma lem3291393 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291394 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291393 _86360 P x). Qed.
Lemma lem3291395 {_86360 : Type'} (r : _86360 -> Prop) (x : _86360) : (@IN _86360 x r) = (r x).
Proof. exact (@lem3291394 _86360 r x). Qed.
Lemma lem3291396 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term26 _86360 q x r) = (term29 _86360 q r x).
Proof. exact (MK_COMB (@lem3291391 _86360 q x) (@lem3291395 _86360 r x)). Qed.
Lemma lem3291399 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term25 _86360 x q r) = (term29 _86360 q r x).
Proof. exact (TRANS (@lem3291383 _86360 q x r) (@lem3291396 _86360 q r x)). Qed.
Lemma lem3291400 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term44 _86360 p x q r) = (term45 _86360 p q r x).
Proof. exact (MK_COMB (@lem3291379 _86360 p x) (@lem3291399 _86360 q r x)). Qed.
Lemma lem3291403 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term43 _86360 x p q r) = (term45 _86360 p q r x).
Proof. exact (TRANS (@lem3291371 _86360 p x q r) (@lem3291400 _86360 p q r x)). Qed.
Lemma lem3291404 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : ((term36 _86360 x p q r) = (term43 _86360 x p q r)) = ((term40 _86360 p q r x) = (term45 _86360 p q r x)).
Proof. exact (MK_COMB (@lem3291367 _86360 p q r x) (@lem3291403 _86360 p q r x)). Qed.
Lemma lem3291407 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term46 _86360 p q r) = (term47 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3291404 _86360 p q r x)). Qed.
Lemma lem3291408 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3291409 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term6 _86360 p q r) = (term48 _86360 p q r).
Proof. exact (MK_COMB (@lem3291408 _86360) (@lem3291407 _86360 p q r)). Qed.
Lemma lem3291414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291415 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term8 _86360 p q r) = (term49 _86360 p q r).
Proof. exact (MK_COMB (@lem3291414) (@lem3291409 _86360 p q r)). Qed.
Lemma lem3291425 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291426 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291425 _86360 s x t). Qed.
Lemma lem3291427 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term43 _86360 x p q r) = (term44 _86360 p x q r).
Proof. exact (@lem3291426 _86360 p x (@INTER _86360 q r)). Qed.
Lemma lem3291431 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291432 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291431 _86360 P x). Qed.
Lemma lem3291433 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291432 _86360 p x). Qed.
Lemma lem3291434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291435 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291434) (@lem3291433 _86360 p x)). Qed.
Lemma lem3291437 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291438 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291437 _86360 s x t). Qed.
Lemma lem3291439 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (r : _86360 -> Prop) : (term25 _86360 x q r) = (term26 _86360 q x r).
Proof. exact (@lem3291438 _86360 q x r). Qed.
Lemma lem3291443 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291444 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291443 _86360 P x). Qed.
Lemma lem3291445 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291444 _86360 q x). Qed.
Lemma lem3291446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291447 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term27 _86360 x q) = (term28 _86360 q x).
Proof. exact (MK_COMB (@lem3291446) (@lem3291445 _86360 q x)). Qed.
Lemma lem3291449 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291450 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291449 _86360 P x). Qed.
Lemma lem3291451 {_86360 : Type'} (r : _86360 -> Prop) (x : _86360) : (@IN _86360 x r) = (r x).
Proof. exact (@lem3291450 _86360 r x). Qed.
Lemma lem3291452 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term26 _86360 q x r) = (term29 _86360 q r x).
Proof. exact (MK_COMB (@lem3291447 _86360 q x) (@lem3291451 _86360 r x)). Qed.
Lemma lem3291455 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term25 _86360 x q r) = (term29 _86360 q r x).
Proof. exact (TRANS (@lem3291439 _86360 q x r) (@lem3291452 _86360 q r x)). Qed.
Lemma lem3291456 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term44 _86360 p x q r) = (term45 _86360 p q r x).
Proof. exact (MK_COMB (@lem3291435 _86360 p x) (@lem3291455 _86360 q r x)). Qed.
Lemma lem3291459 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term43 _86360 x p q r) = (term45 _86360 p q r x).
Proof. exact (TRANS (@lem3291427 _86360 p x q r) (@lem3291456 _86360 p q r x)). Qed.
Lemma lem3291460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291461 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term50 _86360 x p q r) = (term51 _86360 p q r x).
Proof. exact (MK_COMB (@lem3291460) (@lem3291459 _86360 p q r x)). Qed.
Lemma lem3291463 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291464 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291463 _86360 s x t). Qed.
Lemma lem3291465 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term43 _86360 x q p r) = (term44 _86360 q x p r).
Proof. exact (@lem3291464 _86360 q x (@INTER _86360 p r)). Qed.
Lemma lem3291469 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291470 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291469 _86360 P x). Qed.
Lemma lem3291471 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291470 _86360 q x). Qed.
Lemma lem3291472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291473 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term27 _86360 x q) = (term28 _86360 q x).
Proof. exact (MK_COMB (@lem3291472) (@lem3291471 _86360 q x)). Qed.
Lemma lem3291475 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291476 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291475 _86360 s x t). Qed.
Lemma lem3291477 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (r : _86360 -> Prop) : (term25 _86360 x p r) = (term26 _86360 p x r).
Proof. exact (@lem3291476 _86360 p x r). Qed.
Lemma lem3291481 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291482 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291481 _86360 P x). Qed.
Lemma lem3291483 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291482 _86360 p x). Qed.
Lemma lem3291484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291485 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291484) (@lem3291483 _86360 p x)). Qed.
Lemma lem3291487 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291488 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291487 _86360 P x). Qed.
Lemma lem3291489 {_86360 : Type'} (r : _86360 -> Prop) (x : _86360) : (@IN _86360 x r) = (r x).
Proof. exact (@lem3291488 _86360 r x). Qed.
Lemma lem3291490 {_86360 : Type'} (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term26 _86360 p x r) = (term29 _86360 p r x).
Proof. exact (MK_COMB (@lem3291485 _86360 p x) (@lem3291489 _86360 r x)). Qed.
Lemma lem3291493 {_86360 : Type'} (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term25 _86360 x p r) = (term29 _86360 p r x).
Proof. exact (TRANS (@lem3291477 _86360 p x r) (@lem3291490 _86360 p r x)). Qed.
Lemma lem3291494 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term44 _86360 q x p r) = (term45 _86360 q p r x).
Proof. exact (MK_COMB (@lem3291473 _86360 q x) (@lem3291493 _86360 p r x)). Qed.
Lemma lem3291497 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term43 _86360 x q p r) = (term45 _86360 q p r x).
Proof. exact (TRANS (@lem3291465 _86360 q x p r) (@lem3291494 _86360 q p r x)). Qed.
Lemma lem3291498 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : ((term43 _86360 x p q r) = (term43 _86360 x q p r)) = ((term45 _86360 p q r x) = (term45 _86360 q p r x)).
Proof. exact (MK_COMB (@lem3291461 _86360 p q r x) (@lem3291497 _86360 q p r x)). Qed.
Lemma lem3291501 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term52 _86360 q p r) = (term53 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3291498 _86360 q p r x)). Qed.
Lemma lem3291502 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3291503 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term9 _86360 q p r) = (term54 _86360 q p r).
Proof. exact (MK_COMB (@lem3291502 _86360) (@lem3291501 _86360 q p r)). Qed.
Lemma lem3291508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291509 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term11 _86360 q p r) = (term55 _86360 q p r).
Proof. exact (MK_COMB (@lem3291508) (@lem3291503 _86360 q p r)). Qed.
Lemma lem3291519 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291520 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291519 _86360 s x t). Qed.
Lemma lem3291521 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) : (term56 _86360 x p) = (term57 _86360 x p).
Proof. exact (@lem3291520 _86360 p x p). Qed.
Lemma lem3291523 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem3291524 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) : (term57 _86360 x p) = (@IN _86360 x p).
Proof. exact (@lem3291523 (@IN _86360 x p)). Qed.
Lemma lem3291526 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291527 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291526 _86360 P x). Qed.
Lemma lem3291528 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291527 _86360 p x). Qed.
Lemma lem3291529 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term57 _86360 x p) = (p x).
Proof. exact (TRANS (@lem3291524 _86360 x p) (@lem3291528 _86360 p x)). Qed.
Lemma lem3291530 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term56 _86360 x p) = (p x).
Proof. exact (TRANS (@lem3291521 _86360 x p) (@lem3291529 _86360 p x)). Qed.
Lemma lem3291531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291532 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term58 _86360 x p) = (term59 _86360 p x).
Proof. exact (MK_COMB (@lem3291531) (@lem3291530 _86360 p x)). Qed.
Lemma lem3291534 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291535 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291534 _86360 P x). Qed.
Lemma lem3291536 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291535 _86360 p x). Qed.
Lemma lem3291537 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : ((term56 _86360 x p) = (@IN _86360 x p)) = ((p x) = (p x)).
Proof. exact (MK_COMB (@lem3291532 _86360 p x) (@lem3291536 _86360 p x)). Qed.
Lemma lem3291539 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3291540 (x : Prop) : (x = x) = True.
Proof. exact (@lem3291539 Prop x). Qed.
Lemma lem3291541 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : ((p x) = (p x)) = True.
Proof. exact (@lem3291540 (p x)). Qed.
Lemma lem3291542 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) : ((term56 _86360 x p) = (@IN _86360 x p)) = True.
Proof. exact (TRANS (@lem3291537 _86360 p x) (@lem3291541 _86360 p x)). Qed.
Lemma lem3291543 {_86360 : Type'} (p : _86360 -> Prop) : (term60 _86360 p) = (term61 _86360).
Proof. exact (fun_ext (fun x : _86360 => @lem3291542 _86360 x p)). Qed.
Lemma lem3291544 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3291545 {_86360 : Type'} (p : _86360 -> Prop) : (term12 _86360 p) = (term62 _86360).
Proof. exact (MK_COMB (@lem3291544 _86360) (@lem3291543 _86360 p)). Qed.
Lemma lem3291547 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3291548 {_86360 : Type'} (t : Prop) : (term63 _86360 t) = t.
Proof. exact (@lem3291547 _86360 t). Qed.
Lemma lem3291549 {_86360 : Type'} : (term62 _86360) = True.
Proof. exact (@lem3291548 _86360 True). Qed.
Lemma lem3291550 {_86360 : Type'} (p : _86360 -> Prop) : (term12 _86360 p) = True.
Proof. exact (TRANS (@lem3291545 _86360 p) (@lem3291549 _86360)). Qed.
Lemma lem3291551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291552 {_86360 : Type'} (p : _86360 -> Prop) : (term14 _86360 p) = (and True).
Proof. exact (MK_COMB (@lem3291551) (@lem3291550 _86360 p)). Qed.
Lemma lem3291560 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291561 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291560 _86360 s x t). Qed.
Lemma lem3291562 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term64 _86360 x p q) = (term65 _86360 x p q).
Proof. exact (@lem3291561 _86360 p x (@INTER _86360 p q)). Qed.
Lemma lem3291566 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291567 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291566 _86360 P x). Qed.
Lemma lem3291568 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291567 _86360 p x). Qed.
Lemma lem3291569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291570 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291569) (@lem3291568 _86360 p x)). Qed.
Lemma lem3291572 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291573 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291572 _86360 s x t). Qed.
Lemma lem3291574 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (q : _86360 -> Prop) : (term25 _86360 x p q) = (term26 _86360 p x q).
Proof. exact (@lem3291573 _86360 p x q). Qed.
Lemma lem3291578 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291579 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291578 _86360 P x). Qed.
Lemma lem3291580 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291579 _86360 p x). Qed.
Lemma lem3291581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291582 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291581) (@lem3291580 _86360 p x)). Qed.
Lemma lem3291584 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291585 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291584 _86360 P x). Qed.
Lemma lem3291586 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291585 _86360 q x). Qed.
Lemma lem3291587 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term26 _86360 p x q) = (term29 _86360 p q x).
Proof. exact (MK_COMB (@lem3291582 _86360 p x) (@lem3291586 _86360 q x)). Qed.
Lemma lem3291590 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term25 _86360 x p q) = (term29 _86360 p q x).
Proof. exact (TRANS (@lem3291574 _86360 p x q) (@lem3291587 _86360 p q x)). Qed.
Lemma lem3291591 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term65 _86360 x p q) = (term66 _86360 p q x).
Proof. exact (MK_COMB (@lem3291570 _86360 p x) (@lem3291590 _86360 p q x)). Qed.
Lemma lem3291594 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term64 _86360 x p q) = (term66 _86360 p q x).
Proof. exact (TRANS (@lem3291562 _86360 x p q) (@lem3291591 _86360 p q x)). Qed.
Lemma lem3291595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291596 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term67 _86360 x p q) = (term68 _86360 p q x).
Proof. exact (MK_COMB (@lem3291595) (@lem3291594 _86360 p q x)). Qed.
Lemma lem3291598 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3291599 {_86360 : Type'} (s : _86360 -> Prop) (x : _86360) (t : _86360 -> Prop) : (term25 _86360 x s t) = (term26 _86360 s x t).
Proof. exact (@lem3291598 _86360 s x t). Qed.
Lemma lem3291600 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (q : _86360 -> Prop) : (term25 _86360 x p q) = (term26 _86360 p x q).
Proof. exact (@lem3291599 _86360 p x q). Qed.
Lemma lem3291604 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291605 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291604 _86360 P x). Qed.
Lemma lem3291606 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (@IN _86360 x p) = (p x).
Proof. exact (@lem3291605 _86360 p x). Qed.
Lemma lem3291607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291608 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term27 _86360 x p) = (term28 _86360 p x).
Proof. exact (MK_COMB (@lem3291607) (@lem3291606 _86360 p x)). Qed.
Lemma lem3291610 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3291611 {_86360 : Type'} (P : _86360 -> Prop) (x : _86360) : (@IN _86360 x P) = (P x).
Proof. exact (@lem3291610 _86360 P x). Qed.
Lemma lem3291612 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (@IN _86360 x q) = (q x).
Proof. exact (@lem3291611 _86360 q x). Qed.
Lemma lem3291613 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term26 _86360 p x q) = (term29 _86360 p q x).
Proof. exact (MK_COMB (@lem3291608 _86360 p x) (@lem3291612 _86360 q x)). Qed.
Lemma lem3291616 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term25 _86360 x p q) = (term29 _86360 p q x).
Proof. exact (TRANS (@lem3291600 _86360 p x q) (@lem3291613 _86360 p q x)). Qed.
Lemma lem3291617 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : ((term64 _86360 x p q) = (term25 _86360 x p q)) = ((term66 _86360 p q x) = (term29 _86360 p q x)).
Proof. exact (MK_COMB (@lem3291596 _86360 p q x) (@lem3291616 _86360 p q x)). Qed.
Lemma lem3291620 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term69 _86360 p q) = (term70 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3291617 _86360 p q x)). Qed.
Lemma lem3291621 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3291622 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term16 _86360 p q) = (term71 _86360 p q).
Proof. exact (MK_COMB (@lem3291621 _86360) (@lem3291620 _86360 p q)). Qed.
Lemma lem3291627 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term18 _86360 p q) = (term72 _86360 p q).
Proof. exact (MK_COMB (@lem3291552 _86360 p) (@lem3291622 _86360 p q)). Qed.
Lemma lem3291629 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3291630 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term72 _86360 p q) = (term71 _86360 p q).
Proof. exact (@lem3291629 (term71 _86360 p q)). Qed.
Lemma lem3291643 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term18 _86360 p q) = (term71 _86360 p q).
Proof. exact (TRANS (@lem3291627 _86360 p q) (@lem3291630 _86360 p q)). Qed.
Lemma lem3291644 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term20 _86360 r p q) = (term73 _86360 r p q).
Proof. exact (MK_COMB (@lem3291509 _86360 q p r) (@lem3291643 _86360 p q)). Qed.
Lemma lem3291647 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term22 _86360 r p q) = (term74 _86360 r p q).
Proof. exact (MK_COMB (@lem3291415 _86360 p q r) (@lem3291644 _86360 r p q)). Qed.
Lemma lem3291650 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term24 _86360 r p q) = (term75 _86360 r p q).
Proof. exact (MK_COMB (@lem3291321 _86360 q p) (@lem3291647 _86360 r p q)). Qed.
Lemma lem3291653 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term75 _86360 r p q) = (term24 _86360 r p q).
Proof. exact (SYM (@lem3291650 _86360 r p q)). Qed.
Lemma lem3291655 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3291656 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term75 _86360 r p q) = (term77 _86360 r p q).
Proof. exact (@lem3291655 (term75 _86360 r p q)). Qed.
Lemma lem3291657 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term77 _86360 r p q) = (term75 _86360 r p q).
Proof. exact (SYM (@lem3291656 _86360 r p q)). Qed.
Lemma lem3291658 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term78 _86360 r p q) : term78 _86360 r p q.
Proof. exact (h1). Qed.
Lemma lem3291661 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term77 _86360 r p q) : term77 _86360 r p q.
Proof. exact (h1). Qed.
Lemma lem3291662 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term79 _86360 r p q.
Proof. exact (fun h0 : term77 _86360 r p q => @lem3291661 _86360 r p q h0). Qed.
Lemma lem3291663 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term79 _86360 r p q) : term79 _86360 r p q.
Proof. exact (h1). Qed.
Lemma lem3291664 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term77 _86360 r p q) : term77 _86360 r p q.
Proof. exact (h1). Qed.
Lemma lem3291665 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term77 _86360 r p q) (h2 : term79 _86360 r p q) : term77 _86360 r p q.
Proof. exact (@lem3291663 _86360 r p q h2 (@lem3291664 _86360 r p q h1)). Qed.
Lemma lem3291666 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term77 _86360 r p q) : term80 _86360 r p q.
Proof. exact (fun h0 : term79 _86360 r p q => @lem3291665 _86360 r p q h1 h0). Qed.
Lemma lem3291667 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term79 _86360 r p q) : term79 _86360 r p q.
Proof. exact (h1). Qed.
Lemma lem3291668 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term77 _86360 r p q) (h2 : term79 _86360 r p q) : term77 _86360 r p q.
Proof. exact (@lem3291666 _86360 r p q h1 (@lem3291667 _86360 r p q h2)). Qed.
Lemma lem3291669 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term79 _86360 r p q) : term79 _86360 r p q.
Proof. exact (fun h0 : term77 _86360 r p q => @lem3291668 _86360 r p q h0 h1). Qed.
Lemma lem3291670 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term81 _86360 r p q.
Proof. exact (fun h0 : term79 _86360 r p q => @lem3291669 _86360 r p q h0). Qed.
Lemma lem3291673 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term79 _86360 r p q.
Proof. exact (@lem3291670 _86360 r p q (@lem3291662 _86360 r p q)). Qed.
Lemma lem3291674 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term79 _86360 r p q.
Proof. exact (@lem3291673 _86360 r p q). Qed.
Lemma lem3291688 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3291689 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term77 _86360 r p q) = (term82 _86360 r p q).
Proof. exact (@lem3291688 (term78 _86360 r p q)). Qed.
Lemma lem3291691 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3291692 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term82 _86360 r p q) = (term75 _86360 r p q).
Proof. exact (@lem3291691 (term75 _86360 r p q)). Qed.
Lemma lem3291695 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term77 _86360 r p q) = (term75 _86360 r p q).
Proof. exact (TRANS (@lem3291689 _86360 r p q) (@lem3291692 _86360 r p q)). Qed.
Lemma lem3291742 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term84 _86360 p q) = (term85 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291695 _86360 r p q)). Qed.
Lemma lem3291743 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291744 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term86 _86360 p q) = (term87 _86360 p q).
Proof. exact (MK_COMB (@lem3291743 _86360) (@lem3291742 _86360 p q)). Qed.
Lemma lem3291746 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3291747 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3291746 (_86360 -> Prop) P Q). Qed.
Lemma lem3291748 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term92 _86360 p q) = (term93 _86360 p q).
Proof. exact (@lem3291747 _86360 (term94 _86360 q p) (term95 _86360 p q)). Qed.
Lemma lem3291749 {_86360 : Type'} (r : _86360 -> Prop) (q : _86360 -> Prop) (p : _86360 -> Prop) : (term96 _86360 q p r) = (term34 _86360 q p).
Proof. exact (eq_refl (term96 _86360 q p r)). Qed.
Lemma lem3291750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291751 {_86360 : Type'} (r : _86360 -> Prop) (q : _86360 -> Prop) (p : _86360 -> Prop) : (term97 _86360 q p r) = (term35 _86360 q p).
Proof. exact (MK_COMB (@lem3291750) (@lem3291749 _86360 r q p)). Qed.
Lemma lem3291752 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term98 _86360 p q r) = (term74 _86360 r p q).
Proof. exact (eq_refl (term98 _86360 p q r)). Qed.
Lemma lem3291753 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term99 _86360 p q r) = (term75 _86360 r p q).
Proof. exact (MK_COMB (@lem3291751 _86360 r q p) (@lem3291752 _86360 r p q)). Qed.
Lemma lem3291754 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term100 _86360 p q) = (term85 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291753 _86360 r p q)). Qed.
Lemma lem3291755 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291756 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term92 _86360 p q) = (term87 _86360 p q).
Proof. exact (MK_COMB (@lem3291755 _86360) (@lem3291754 _86360 p q)). Qed.
Lemma lem3291757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291758 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term101 _86360 p q) = (term102 _86360 p q).
Proof. exact (MK_COMB (@lem3291757) (@lem3291756 _86360 p q)). Qed.
Lemma lem3291759 {_86360 : Type'} (r : _86360 -> Prop) (q : _86360 -> Prop) (p : _86360 -> Prop) : (term96 _86360 q p r) = (term34 _86360 q p).
Proof. exact (eq_refl (term96 _86360 q p r)). Qed.
Lemma lem3291760 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term103 _86360 q p) = (term94 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291759 _86360 r q p)). Qed.
Lemma lem3291761 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291762 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term104 _86360 q p) = (term105 _86360 q p).
Proof. exact (MK_COMB (@lem3291761 _86360) (@lem3291760 _86360 q p)). Qed.
Lemma lem3291763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291764 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term106 _86360 q p) = (term107 _86360 q p).
Proof. exact (MK_COMB (@lem3291763) (@lem3291762 _86360 q p)). Qed.
Lemma lem3291765 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term98 _86360 p q r) = (term74 _86360 r p q).
Proof. exact (eq_refl (term98 _86360 p q r)). Qed.
Lemma lem3291766 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term108 _86360 p q) = (term95 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291765 _86360 r p q)). Qed.
Lemma lem3291767 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291768 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term109 _86360 p q) = (term110 _86360 p q).
Proof. exact (MK_COMB (@lem3291767 _86360) (@lem3291766 _86360 p q)). Qed.
Lemma lem3291769 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term93 _86360 p q) = (term111 _86360 p q).
Proof. exact (MK_COMB (@lem3291764 _86360 q p) (@lem3291768 _86360 p q)). Qed.
Lemma lem3291770 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term92 _86360 p q) = (term93 _86360 p q)) = ((term87 _86360 p q) = (term111 _86360 p q)).
Proof. exact (MK_COMB (@lem3291758 _86360 p q) (@lem3291769 _86360 p q)). Qed.
Lemma lem3291771 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term87 _86360 p q) = (term111 _86360 p q).
Proof. exact (EQ_MP (@lem3291770 _86360 p q) (@lem3291748 _86360 p q)). Qed.
Lemma lem3291775 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem3291776 {_86360 : Type'} (t : Prop) : (term112 _86360 t) = t.
Proof. exact (@lem3291775 (_86360 -> Prop) t). Qed.
Lemma lem3291777 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term105 _86360 q p) = (term34 _86360 q p).
Proof. exact (@lem3291776 _86360 (term34 _86360 q p)). Qed.
Lemma lem3291786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291787 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term107 _86360 q p) = (term35 _86360 q p).
Proof. exact (MK_COMB (@lem3291786) (@lem3291777 _86360 q p)). Qed.
Lemma lem3291789 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3291790 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3291789 (_86360 -> Prop) P Q). Qed.
Lemma lem3291791 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term113 _86360 p q) = (term114 _86360 p q).
Proof. exact (@lem3291790 _86360 (term115 _86360 p q) (term116 _86360 p q)). Qed.
Lemma lem3291792 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term117 _86360 p q r) = (term48 _86360 p q r).
Proof. exact (eq_refl (term117 _86360 p q r)). Qed.
Lemma lem3291793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291794 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term118 _86360 p q r) = (term49 _86360 p q r).
Proof. exact (MK_COMB (@lem3291793) (@lem3291792 _86360 p q r)). Qed.
Lemma lem3291795 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term119 _86360 p q r) = (term73 _86360 r p q).
Proof. exact (eq_refl (term119 _86360 p q r)). Qed.
Lemma lem3291796 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term120 _86360 p q r) = (term74 _86360 r p q).
Proof. exact (MK_COMB (@lem3291794 _86360 p q r) (@lem3291795 _86360 r p q)). Qed.
Lemma lem3291797 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term121 _86360 p q) = (term95 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291796 _86360 r p q)). Qed.
Lemma lem3291798 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291799 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term113 _86360 p q) = (term110 _86360 p q).
Proof. exact (MK_COMB (@lem3291798 _86360) (@lem3291797 _86360 p q)). Qed.
Lemma lem3291800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291801 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term122 _86360 p q) = (term123 _86360 p q).
Proof. exact (MK_COMB (@lem3291800) (@lem3291799 _86360 p q)). Qed.
Lemma lem3291802 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term117 _86360 p q r) = (term48 _86360 p q r).
Proof. exact (eq_refl (term117 _86360 p q r)). Qed.
Lemma lem3291803 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term124 _86360 p q) = (term115 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291802 _86360 p q r)). Qed.
Lemma lem3291804 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291805 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term125 _86360 p q) = (term126 _86360 p q).
Proof. exact (MK_COMB (@lem3291804 _86360) (@lem3291803 _86360 p q)). Qed.
Lemma lem3291806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291807 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term127 _86360 p q) = (term128 _86360 p q).
Proof. exact (MK_COMB (@lem3291806) (@lem3291805 _86360 p q)). Qed.
Lemma lem3291808 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term119 _86360 p q r) = (term73 _86360 r p q).
Proof. exact (eq_refl (term119 _86360 p q r)). Qed.
Lemma lem3291809 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term129 _86360 p q) = (term116 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291808 _86360 r p q)). Qed.
Lemma lem3291810 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291811 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term130 _86360 p q) = (term131 _86360 p q).
Proof. exact (MK_COMB (@lem3291810 _86360) (@lem3291809 _86360 p q)). Qed.
Lemma lem3291812 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term114 _86360 p q) = (term132 _86360 p q).
Proof. exact (MK_COMB (@lem3291807 _86360 p q) (@lem3291811 _86360 p q)). Qed.
Lemma lem3291813 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term113 _86360 p q) = (term114 _86360 p q)) = ((term110 _86360 p q) = (term132 _86360 p q)).
Proof. exact (MK_COMB (@lem3291801 _86360 p q) (@lem3291812 _86360 p q)). Qed.
Lemma lem3291814 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term110 _86360 p q) = (term132 _86360 p q).
Proof. exact (EQ_MP (@lem3291813 _86360 p q) (@lem3291791 _86360 p q)). Qed.
Lemma lem3291834 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3291835 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3291834 (_86360 -> Prop) P Q). Qed.
Lemma lem3291836 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term133 _86360 p q) = (term134 _86360 p q).
Proof. exact (@lem3291835 _86360 (term135 _86360 q p) (term136 _86360 p q)). Qed.
Lemma lem3291837 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term137 _86360 q p r) = (term54 _86360 q p r).
Proof. exact (eq_refl (term137 _86360 q p r)). Qed.
Lemma lem3291838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291839 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term138 _86360 q p r) = (term55 _86360 q p r).
Proof. exact (MK_COMB (@lem3291838) (@lem3291837 _86360 q p r)). Qed.
Lemma lem3291840 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term139 _86360 p q r) = (term71 _86360 p q).
Proof. exact (eq_refl (term139 _86360 p q r)). Qed.
Lemma lem3291841 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term140 _86360 p q r) = (term73 _86360 r p q).
Proof. exact (MK_COMB (@lem3291839 _86360 q p r) (@lem3291840 _86360 r p q)). Qed.
Lemma lem3291842 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term141 _86360 p q) = (term116 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291841 _86360 r p q)). Qed.
Lemma lem3291843 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291844 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term133 _86360 p q) = (term131 _86360 p q).
Proof. exact (MK_COMB (@lem3291843 _86360) (@lem3291842 _86360 p q)). Qed.
Lemma lem3291845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291846 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term142 _86360 p q) = (term143 _86360 p q).
Proof. exact (MK_COMB (@lem3291845) (@lem3291844 _86360 p q)). Qed.
Lemma lem3291847 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term137 _86360 q p r) = (term54 _86360 q p r).
Proof. exact (eq_refl (term137 _86360 q p r)). Qed.
Lemma lem3291848 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term144 _86360 q p) = (term135 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291847 _86360 q p r)). Qed.
Lemma lem3291849 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291850 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term145 _86360 q p) = (term146 _86360 q p).
Proof. exact (MK_COMB (@lem3291849 _86360) (@lem3291848 _86360 q p)). Qed.
Lemma lem3291851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291852 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term147 _86360 q p) = (term148 _86360 q p).
Proof. exact (MK_COMB (@lem3291851) (@lem3291850 _86360 q p)). Qed.
Lemma lem3291853 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term139 _86360 p q r) = (term71 _86360 p q).
Proof. exact (eq_refl (term139 _86360 p q r)). Qed.
Lemma lem3291854 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term149 _86360 p q) = (term136 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3291853 _86360 r p q)). Qed.
Lemma lem3291855 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291856 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term150 _86360 p q) = (term151 _86360 p q).
Proof. exact (MK_COMB (@lem3291855 _86360) (@lem3291854 _86360 p q)). Qed.
Lemma lem3291857 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term134 _86360 p q) = (term152 _86360 p q).
Proof. exact (MK_COMB (@lem3291852 _86360 q p) (@lem3291856 _86360 p q)). Qed.
Lemma lem3291858 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term133 _86360 p q) = (term134 _86360 p q)) = ((term131 _86360 p q) = (term152 _86360 p q)).
Proof. exact (MK_COMB (@lem3291846 _86360 p q) (@lem3291857 _86360 p q)). Qed.
Lemma lem3291859 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term131 _86360 p q) = (term152 _86360 p q).
Proof. exact (EQ_MP (@lem3291858 _86360 p q) (@lem3291836 _86360 p q)). Qed.
Lemma lem3291879 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem3291880 {_86360 : Type'} (t : Prop) : (term112 _86360 t) = t.
Proof. exact (@lem3291879 (_86360 -> Prop) t). Qed.
Lemma lem3291881 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term151 _86360 p q) = (term71 _86360 p q).
Proof. exact (@lem3291880 _86360 (term71 _86360 p q)). Qed.
Lemma lem3291892 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term148 _86360 q p) = (term148 _86360 q p).
Proof. exact (eq_refl (term148 _86360 q p)). Qed.
Lemma lem3291893 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term152 _86360 p q) = (term153 _86360 p q).
Proof. exact (MK_COMB (@lem3291892 _86360 q p) (@lem3291881 _86360 p q)). Qed.
Lemma lem3291896 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term131 _86360 p q) = (term153 _86360 p q).
Proof. exact (TRANS (@lem3291859 _86360 p q) (@lem3291893 _86360 p q)). Qed.
Lemma lem3291897 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term128 _86360 p q) = (term128 _86360 p q).
Proof. exact (eq_refl (term128 _86360 p q)). Qed.
Lemma lem3291898 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term132 _86360 p q) = (term154 _86360 p q).
Proof. exact (MK_COMB (@lem3291897 _86360 p q) (@lem3291896 _86360 p q)). Qed.
Lemma lem3291901 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term110 _86360 p q) = (term154 _86360 p q).
Proof. exact (TRANS (@lem3291814 _86360 p q) (@lem3291898 _86360 p q)). Qed.
Lemma lem3291902 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term111 _86360 p q) = (term155 _86360 p q).
Proof. exact (MK_COMB (@lem3291787 _86360 q p) (@lem3291901 _86360 p q)). Qed.
Lemma lem3291905 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term87 _86360 p q) = (term155 _86360 p q).
Proof. exact (TRANS (@lem3291771 _86360 p q) (@lem3291902 _86360 p q)). Qed.
Lemma lem3291906 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term86 _86360 p q) = (term155 _86360 p q).
Proof. exact (TRANS (@lem3291744 _86360 p q) (@lem3291905 _86360 p q)). Qed.
Lemma lem3291907 {_86360 : Type'} (q : _86360 -> Prop) : (term156 _86360 q) = (term157 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291906 _86360 p q)). Qed.
Lemma lem3291908 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291909 {_86360 : Type'} (q : _86360 -> Prop) : (term158 _86360 q) = (term159 _86360 q).
Proof. exact (MK_COMB (@lem3291908 _86360) (@lem3291907 _86360 q)). Qed.
Lemma lem3291911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3291912 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3291911 (_86360 -> Prop) P Q). Qed.
Lemma lem3291913 {_86360 : Type'} (q : _86360 -> Prop) : (term160 _86360 q) = (term161 _86360 q).
Proof. exact (@lem3291912 _86360 (term162 _86360 q) (term163 _86360 q)). Qed.
Lemma lem3291914 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term164 _86360 q p) = (term34 _86360 q p).
Proof. exact (eq_refl (term164 _86360 q p)). Qed.
Lemma lem3291915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291916 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term165 _86360 q p) = (term35 _86360 q p).
Proof. exact (MK_COMB (@lem3291915) (@lem3291914 _86360 q p)). Qed.
Lemma lem3291917 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term166 _86360 q p) = (term154 _86360 p q).
Proof. exact (eq_refl (term166 _86360 q p)). Qed.
Lemma lem3291918 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term167 _86360 q p) = (term155 _86360 p q).
Proof. exact (MK_COMB (@lem3291916 _86360 q p) (@lem3291917 _86360 p q)). Qed.
Lemma lem3291919 {_86360 : Type'} (q : _86360 -> Prop) : (term168 _86360 q) = (term157 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291918 _86360 p q)). Qed.
Lemma lem3291920 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291921 {_86360 : Type'} (q : _86360 -> Prop) : (term160 _86360 q) = (term159 _86360 q).
Proof. exact (MK_COMB (@lem3291920 _86360) (@lem3291919 _86360 q)). Qed.
Lemma lem3291922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291923 {_86360 : Type'} (q : _86360 -> Prop) : (term169 _86360 q) = (term170 _86360 q).
Proof. exact (MK_COMB (@lem3291922) (@lem3291921 _86360 q)). Qed.
Lemma lem3291924 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term164 _86360 q p) = (term34 _86360 q p).
Proof. exact (eq_refl (term164 _86360 q p)). Qed.
Lemma lem3291925 {_86360 : Type'} (q : _86360 -> Prop) : (term171 _86360 q) = (term162 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291924 _86360 q p)). Qed.
Lemma lem3291926 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291927 {_86360 : Type'} (q : _86360 -> Prop) : (term172 _86360 q) = (term173 _86360 q).
Proof. exact (MK_COMB (@lem3291926 _86360) (@lem3291925 _86360 q)). Qed.
Lemma lem3291928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291929 {_86360 : Type'} (q : _86360 -> Prop) : (term174 _86360 q) = (term175 _86360 q).
Proof. exact (MK_COMB (@lem3291928) (@lem3291927 _86360 q)). Qed.
Lemma lem3291930 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term166 _86360 q p) = (term154 _86360 p q).
Proof. exact (eq_refl (term166 _86360 q p)). Qed.
Lemma lem3291931 {_86360 : Type'} (q : _86360 -> Prop) : (term176 _86360 q) = (term163 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291930 _86360 p q)). Qed.
Lemma lem3291932 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291933 {_86360 : Type'} (q : _86360 -> Prop) : (term177 _86360 q) = (term178 _86360 q).
Proof. exact (MK_COMB (@lem3291932 _86360) (@lem3291931 _86360 q)). Qed.
Lemma lem3291934 {_86360 : Type'} (q : _86360 -> Prop) : (term161 _86360 q) = (term179 _86360 q).
Proof. exact (MK_COMB (@lem3291929 _86360 q) (@lem3291933 _86360 q)). Qed.
Lemma lem3291935 {_86360 : Type'} (q : _86360 -> Prop) : ((term160 _86360 q) = (term161 _86360 q)) = ((term159 _86360 q) = (term179 _86360 q)).
Proof. exact (MK_COMB (@lem3291923 _86360 q) (@lem3291934 _86360 q)). Qed.
Lemma lem3291936 {_86360 : Type'} (q : _86360 -> Prop) : (term159 _86360 q) = (term179 _86360 q).
Proof. exact (EQ_MP (@lem3291935 _86360 q) (@lem3291913 _86360 q)). Qed.
Lemma lem3291952 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3291953 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3291952 (_86360 -> Prop) P Q). Qed.
Lemma lem3291954 {_86360 : Type'} (q : _86360 -> Prop) : (term180 _86360 q) = (term181 _86360 q).
Proof. exact (@lem3291953 _86360 (term182 _86360 q) (term183 _86360 q)). Qed.
Lemma lem3291955 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term184 _86360 q p) = (term126 _86360 p q).
Proof. exact (eq_refl (term184 _86360 q p)). Qed.
Lemma lem3291956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291957 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term185 _86360 q p) = (term128 _86360 p q).
Proof. exact (MK_COMB (@lem3291956) (@lem3291955 _86360 p q)). Qed.
Lemma lem3291958 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term186 _86360 q p) = (term153 _86360 p q).
Proof. exact (eq_refl (term186 _86360 q p)). Qed.
Lemma lem3291959 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term187 _86360 q p) = (term154 _86360 p q).
Proof. exact (MK_COMB (@lem3291957 _86360 p q) (@lem3291958 _86360 p q)). Qed.
Lemma lem3291960 {_86360 : Type'} (q : _86360 -> Prop) : (term188 _86360 q) = (term163 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291959 _86360 p q)). Qed.
Lemma lem3291961 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291962 {_86360 : Type'} (q : _86360 -> Prop) : (term180 _86360 q) = (term178 _86360 q).
Proof. exact (MK_COMB (@lem3291961 _86360) (@lem3291960 _86360 q)). Qed.
Lemma lem3291963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3291964 {_86360 : Type'} (q : _86360 -> Prop) : (term189 _86360 q) = (term190 _86360 q).
Proof. exact (MK_COMB (@lem3291963) (@lem3291962 _86360 q)). Qed.
Lemma lem3291965 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term184 _86360 q p) = (term126 _86360 p q).
Proof. exact (eq_refl (term184 _86360 q p)). Qed.
Lemma lem3291966 {_86360 : Type'} (q : _86360 -> Prop) : (term191 _86360 q) = (term182 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291965 _86360 p q)). Qed.
Lemma lem3291967 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291968 {_86360 : Type'} (q : _86360 -> Prop) : (term192 _86360 q) = (term193 _86360 q).
Proof. exact (MK_COMB (@lem3291967 _86360) (@lem3291966 _86360 q)). Qed.
Lemma lem3291969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291970 {_86360 : Type'} (q : _86360 -> Prop) : (term194 _86360 q) = (term195 _86360 q).
Proof. exact (MK_COMB (@lem3291969) (@lem3291968 _86360 q)). Qed.
Lemma lem3291971 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term186 _86360 q p) = (term153 _86360 p q).
Proof. exact (eq_refl (term186 _86360 q p)). Qed.
Lemma lem3291972 {_86360 : Type'} (q : _86360 -> Prop) : (term196 _86360 q) = (term183 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3291971 _86360 p q)). Qed.
Lemma lem3291973 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3291974 {_86360 : Type'} (q : _86360 -> Prop) : (term197 _86360 q) = (term198 _86360 q).
Proof. exact (MK_COMB (@lem3291973 _86360) (@lem3291972 _86360 q)). Qed.
Lemma lem3291975 {_86360 : Type'} (q : _86360 -> Prop) : (term181 _86360 q) = (term199 _86360 q).
Proof. exact (MK_COMB (@lem3291970 _86360 q) (@lem3291974 _86360 q)). Qed.
Lemma lem3291976 {_86360 : Type'} (q : _86360 -> Prop) : ((term180 _86360 q) = (term181 _86360 q)) = ((term178 _86360 q) = (term199 _86360 q)).
Proof. exact (MK_COMB (@lem3291964 _86360 q) (@lem3291975 _86360 q)). Qed.
Lemma lem3291977 {_86360 : Type'} (q : _86360 -> Prop) : (term178 _86360 q) = (term199 _86360 q).
Proof. exact (EQ_MP (@lem3291976 _86360 q) (@lem3291954 _86360 q)). Qed.
Lemma lem3292001 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3292002 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3292001 (_86360 -> Prop) P Q). Qed.
Lemma lem3292003 {_86360 : Type'} (q : _86360 -> Prop) : (term200 _86360 q) = (term201 _86360 q).
Proof. exact (@lem3292002 _86360 (term202 _86360 q) (term203 _86360 q)). Qed.
Lemma lem3292004 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term204 _86360 q p) = (term146 _86360 q p).
Proof. exact (eq_refl (term204 _86360 q p)). Qed.
Lemma lem3292005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292006 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term205 _86360 q p) = (term148 _86360 q p).
Proof. exact (MK_COMB (@lem3292005) (@lem3292004 _86360 q p)). Qed.
Lemma lem3292007 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term206 _86360 q p) = (term71 _86360 p q).
Proof. exact (eq_refl (term206 _86360 q p)). Qed.
Lemma lem3292008 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term207 _86360 q p) = (term153 _86360 p q).
Proof. exact (MK_COMB (@lem3292006 _86360 q p) (@lem3292007 _86360 p q)). Qed.
Lemma lem3292009 {_86360 : Type'} (q : _86360 -> Prop) : (term208 _86360 q) = (term183 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292008 _86360 p q)). Qed.
Lemma lem3292010 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292011 {_86360 : Type'} (q : _86360 -> Prop) : (term200 _86360 q) = (term198 _86360 q).
Proof. exact (MK_COMB (@lem3292010 _86360) (@lem3292009 _86360 q)). Qed.
Lemma lem3292012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3292013 {_86360 : Type'} (q : _86360 -> Prop) : (term209 _86360 q) = (term210 _86360 q).
Proof. exact (MK_COMB (@lem3292012) (@lem3292011 _86360 q)). Qed.
Lemma lem3292014 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term204 _86360 q p) = (term146 _86360 q p).
Proof. exact (eq_refl (term204 _86360 q p)). Qed.
Lemma lem3292015 {_86360 : Type'} (q : _86360 -> Prop) : (term211 _86360 q) = (term202 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292014 _86360 q p)). Qed.
Lemma lem3292016 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292017 {_86360 : Type'} (q : _86360 -> Prop) : (term212 _86360 q) = (term213 _86360 q).
Proof. exact (MK_COMB (@lem3292016 _86360) (@lem3292015 _86360 q)). Qed.
Lemma lem3292018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292019 {_86360 : Type'} (q : _86360 -> Prop) : (term214 _86360 q) = (term215 _86360 q).
Proof. exact (MK_COMB (@lem3292018) (@lem3292017 _86360 q)). Qed.
Lemma lem3292020 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term206 _86360 q p) = (term71 _86360 p q).
Proof. exact (eq_refl (term206 _86360 q p)). Qed.
Lemma lem3292021 {_86360 : Type'} (q : _86360 -> Prop) : (term216 _86360 q) = (term203 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292020 _86360 p q)). Qed.
Lemma lem3292022 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292023 {_86360 : Type'} (q : _86360 -> Prop) : (term217 _86360 q) = (term218 _86360 q).
Proof. exact (MK_COMB (@lem3292022 _86360) (@lem3292021 _86360 q)). Qed.
Lemma lem3292024 {_86360 : Type'} (q : _86360 -> Prop) : (term201 _86360 q) = (term219 _86360 q).
Proof. exact (MK_COMB (@lem3292019 _86360 q) (@lem3292023 _86360 q)). Qed.
Lemma lem3292025 {_86360 : Type'} (q : _86360 -> Prop) : ((term200 _86360 q) = (term201 _86360 q)) = ((term198 _86360 q) = (term219 _86360 q)).
Proof. exact (MK_COMB (@lem3292013 _86360 q) (@lem3292024 _86360 q)). Qed.
Lemma lem3292026 {_86360 : Type'} (q : _86360 -> Prop) : (term198 _86360 q) = (term219 _86360 q).
Proof. exact (EQ_MP (@lem3292025 _86360 q) (@lem3292003 _86360 q)). Qed.
Lemma lem3292063 {_86360 : Type'} (q : _86360 -> Prop) : (term195 _86360 q) = (term195 _86360 q).
Proof. exact (eq_refl (term195 _86360 q)). Qed.
Lemma lem3292064 {_86360 : Type'} (q : _86360 -> Prop) : (term199 _86360 q) = (term220 _86360 q).
Proof. exact (MK_COMB (@lem3292063 _86360 q) (@lem3292026 _86360 q)). Qed.
Lemma lem3292067 {_86360 : Type'} (q : _86360 -> Prop) : (term178 _86360 q) = (term220 _86360 q).
Proof. exact (TRANS (@lem3291977 _86360 q) (@lem3292064 _86360 q)). Qed.
Lemma lem3292068 {_86360 : Type'} (q : _86360 -> Prop) : (term175 _86360 q) = (term175 _86360 q).
Proof. exact (eq_refl (term175 _86360 q)). Qed.
Lemma lem3292069 {_86360 : Type'} (q : _86360 -> Prop) : (term179 _86360 q) = (term221 _86360 q).
Proof. exact (MK_COMB (@lem3292068 _86360 q) (@lem3292067 _86360 q)). Qed.
Lemma lem3292072 {_86360 : Type'} (q : _86360 -> Prop) : (term159 _86360 q) = (term221 _86360 q).
Proof. exact (TRANS (@lem3291936 _86360 q) (@lem3292069 _86360 q)). Qed.
Lemma lem3292073 {_86360 : Type'} (q : _86360 -> Prop) : (term158 _86360 q) = (term221 _86360 q).
Proof. exact (TRANS (@lem3291909 _86360 q) (@lem3292072 _86360 q)). Qed.
Lemma lem3292074 {_86360 : Type'} : (term222 _86360) = (term223 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292073 _86360 q)). Qed.
Lemma lem3292075 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292076 {_86360 : Type'} : (term224 _86360) = (term225 _86360).
Proof. exact (MK_COMB (@lem3292075 _86360) (@lem3292074 _86360)). Qed.
Lemma lem3292078 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3292079 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3292078 (_86360 -> Prop) P Q). Qed.
Lemma lem3292080 {_86360 : Type'} : (term226 _86360) = (term227 _86360).
Proof. exact (@lem3292079 _86360 (term228 _86360) (term229 _86360)). Qed.
Lemma lem3292081 {_86360 : Type'} (q : _86360 -> Prop) : (term230 _86360 q) = (term173 _86360 q).
Proof. exact (eq_refl (term230 _86360 q)). Qed.
Lemma lem3292082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292083 {_86360 : Type'} (q : _86360 -> Prop) : (term231 _86360 q) = (term175 _86360 q).
Proof. exact (MK_COMB (@lem3292082) (@lem3292081 _86360 q)). Qed.
Lemma lem3292084 {_86360 : Type'} (q : _86360 -> Prop) : (term232 _86360 q) = (term220 _86360 q).
Proof. exact (eq_refl (term232 _86360 q)). Qed.
Lemma lem3292085 {_86360 : Type'} (q : _86360 -> Prop) : (term233 _86360 q) = (term221 _86360 q).
Proof. exact (MK_COMB (@lem3292083 _86360 q) (@lem3292084 _86360 q)). Qed.
Lemma lem3292086 {_86360 : Type'} : (term234 _86360) = (term223 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292085 _86360 q)). Qed.
Lemma lem3292087 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292088 {_86360 : Type'} : (term226 _86360) = (term225 _86360).
Proof. exact (MK_COMB (@lem3292087 _86360) (@lem3292086 _86360)). Qed.
Lemma lem3292089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3292090 {_86360 : Type'} : (term235 _86360) = (term236 _86360).
Proof. exact (MK_COMB (@lem3292089) (@lem3292088 _86360)). Qed.
Lemma lem3292091 {_86360 : Type'} (q : _86360 -> Prop) : (term230 _86360 q) = (term173 _86360 q).
Proof. exact (eq_refl (term230 _86360 q)). Qed.
Lemma lem3292092 {_86360 : Type'} : (term237 _86360) = (term228 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292091 _86360 q)). Qed.
Lemma lem3292093 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292094 {_86360 : Type'} : (term238 _86360) = (term239 _86360).
Proof. exact (MK_COMB (@lem3292093 _86360) (@lem3292092 _86360)). Qed.
Lemma lem3292095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292096 {_86360 : Type'} : (term240 _86360) = (term241 _86360).
Proof. exact (MK_COMB (@lem3292095) (@lem3292094 _86360)). Qed.
Lemma lem3292097 {_86360 : Type'} (q : _86360 -> Prop) : (term232 _86360 q) = (term220 _86360 q).
Proof. exact (eq_refl (term232 _86360 q)). Qed.
Lemma lem3292098 {_86360 : Type'} : (term242 _86360) = (term229 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292097 _86360 q)). Qed.
Lemma lem3292099 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292100 {_86360 : Type'} : (term243 _86360) = (term244 _86360).
Proof. exact (MK_COMB (@lem3292099 _86360) (@lem3292098 _86360)). Qed.
Lemma lem3292101 {_86360 : Type'} : (term227 _86360) = (term245 _86360).
Proof. exact (MK_COMB (@lem3292096 _86360) (@lem3292100 _86360)). Qed.
Lemma lem3292102 {_86360 : Type'} : ((term226 _86360) = (term227 _86360)) = ((term225 _86360) = (term245 _86360)).
Proof. exact (MK_COMB (@lem3292090 _86360) (@lem3292101 _86360)). Qed.
Lemma lem3292103 {_86360 : Type'} : (term225 _86360) = (term245 _86360).
Proof. exact (EQ_MP (@lem3292102 _86360) (@lem3292080 _86360)). Qed.
Lemma lem3292123 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3292124 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3292123 (_86360 -> Prop) P Q). Qed.
Lemma lem3292125 {_86360 : Type'} : (term246 _86360) = (term247 _86360).
Proof. exact (@lem3292124 _86360 (term248 _86360) (term249 _86360)). Qed.
Lemma lem3292126 {_86360 : Type'} (q : _86360 -> Prop) : (term250 _86360 q) = (term193 _86360 q).
Proof. exact (eq_refl (term250 _86360 q)). Qed.
Lemma lem3292127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292128 {_86360 : Type'} (q : _86360 -> Prop) : (term251 _86360 q) = (term195 _86360 q).
Proof. exact (MK_COMB (@lem3292127) (@lem3292126 _86360 q)). Qed.
Lemma lem3292129 {_86360 : Type'} (q : _86360 -> Prop) : (term252 _86360 q) = (term219 _86360 q).
Proof. exact (eq_refl (term252 _86360 q)). Qed.
Lemma lem3292130 {_86360 : Type'} (q : _86360 -> Prop) : (term253 _86360 q) = (term220 _86360 q).
Proof. exact (MK_COMB (@lem3292128 _86360 q) (@lem3292129 _86360 q)). Qed.
Lemma lem3292131 {_86360 : Type'} : (term254 _86360) = (term229 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292130 _86360 q)). Qed.
Lemma lem3292132 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292133 {_86360 : Type'} : (term246 _86360) = (term244 _86360).
Proof. exact (MK_COMB (@lem3292132 _86360) (@lem3292131 _86360)). Qed.
Lemma lem3292134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3292135 {_86360 : Type'} : (term255 _86360) = (term256 _86360).
Proof. exact (MK_COMB (@lem3292134) (@lem3292133 _86360)). Qed.
Lemma lem3292136 {_86360 : Type'} (q : _86360 -> Prop) : (term250 _86360 q) = (term193 _86360 q).
Proof. exact (eq_refl (term250 _86360 q)). Qed.
Lemma lem3292137 {_86360 : Type'} : (term257 _86360) = (term248 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292136 _86360 q)). Qed.
Lemma lem3292138 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292139 {_86360 : Type'} : (term258 _86360) = (term259 _86360).
Proof. exact (MK_COMB (@lem3292138 _86360) (@lem3292137 _86360)). Qed.
Lemma lem3292140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292141 {_86360 : Type'} : (term260 _86360) = (term261 _86360).
Proof. exact (MK_COMB (@lem3292140) (@lem3292139 _86360)). Qed.
Lemma lem3292142 {_86360 : Type'} (q : _86360 -> Prop) : (term252 _86360 q) = (term219 _86360 q).
Proof. exact (eq_refl (term252 _86360 q)). Qed.
Lemma lem3292143 {_86360 : Type'} : (term262 _86360) = (term249 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292142 _86360 q)). Qed.
Lemma lem3292144 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292145 {_86360 : Type'} : (term263 _86360) = (term264 _86360).
Proof. exact (MK_COMB (@lem3292144 _86360) (@lem3292143 _86360)). Qed.
Lemma lem3292146 {_86360 : Type'} : (term247 _86360) = (term265 _86360).
Proof. exact (MK_COMB (@lem3292141 _86360) (@lem3292145 _86360)). Qed.
Lemma lem3292147 {_86360 : Type'} : ((term246 _86360) = (term247 _86360)) = ((term244 _86360) = (term265 _86360)).
Proof. exact (MK_COMB (@lem3292135 _86360) (@lem3292146 _86360)). Qed.
Lemma lem3292148 {_86360 : Type'} : (term244 _86360) = (term265 _86360).
Proof. exact (EQ_MP (@lem3292147 _86360) (@lem3292125 _86360)). Qed.
Lemma lem3292176 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3292177 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term90 _86360 P Q) = (term91 _86360 P Q).
Proof. exact (@lem3292176 (_86360 -> Prop) P Q). Qed.
Lemma lem3292178 {_86360 : Type'} : (term266 _86360) = (term267 _86360).
Proof. exact (@lem3292177 _86360 (term268 _86360) (term269 _86360)). Qed.
Lemma lem3292179 {_86360 : Type'} (q : _86360 -> Prop) : (term270 _86360 q) = (term213 _86360 q).
Proof. exact (eq_refl (term270 _86360 q)). Qed.
Lemma lem3292180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292181 {_86360 : Type'} (q : _86360 -> Prop) : (term271 _86360 q) = (term215 _86360 q).
Proof. exact (MK_COMB (@lem3292180) (@lem3292179 _86360 q)). Qed.
Lemma lem3292182 {_86360 : Type'} (q : _86360 -> Prop) : (term272 _86360 q) = (term218 _86360 q).
Proof. exact (eq_refl (term272 _86360 q)). Qed.
Lemma lem3292183 {_86360 : Type'} (q : _86360 -> Prop) : (term273 _86360 q) = (term219 _86360 q).
Proof. exact (MK_COMB (@lem3292181 _86360 q) (@lem3292182 _86360 q)). Qed.
Lemma lem3292184 {_86360 : Type'} : (term274 _86360) = (term249 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292183 _86360 q)). Qed.
Lemma lem3292185 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292186 {_86360 : Type'} : (term266 _86360) = (term264 _86360).
Proof. exact (MK_COMB (@lem3292185 _86360) (@lem3292184 _86360)). Qed.
Lemma lem3292187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3292188 {_86360 : Type'} : (term275 _86360) = (term276 _86360).
Proof. exact (MK_COMB (@lem3292187) (@lem3292186 _86360)). Qed.
Lemma lem3292189 {_86360 : Type'} (q : _86360 -> Prop) : (term270 _86360 q) = (term213 _86360 q).
Proof. exact (eq_refl (term270 _86360 q)). Qed.
Lemma lem3292190 {_86360 : Type'} : (term277 _86360) = (term268 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292189 _86360 q)). Qed.
Lemma lem3292191 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292192 {_86360 : Type'} : (term278 _86360) = (term279 _86360).
Proof. exact (MK_COMB (@lem3292191 _86360) (@lem3292190 _86360)). Qed.
Lemma lem3292193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292194 {_86360 : Type'} : (term280 _86360) = (term281 _86360).
Proof. exact (MK_COMB (@lem3292193) (@lem3292192 _86360)). Qed.
Lemma lem3292195 {_86360 : Type'} (q : _86360 -> Prop) : (term272 _86360 q) = (term218 _86360 q).
Proof. exact (eq_refl (term272 _86360 q)). Qed.
Lemma lem3292196 {_86360 : Type'} : (term282 _86360) = (term269 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292195 _86360 q)). Qed.
Lemma lem3292197 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292198 {_86360 : Type'} : (term283 _86360) = (term284 _86360).
Proof. exact (MK_COMB (@lem3292197 _86360) (@lem3292196 _86360)). Qed.
Lemma lem3292199 {_86360 : Type'} : (term267 _86360) = (term285 _86360).
Proof. exact (MK_COMB (@lem3292194 _86360) (@lem3292198 _86360)). Qed.
Lemma lem3292200 {_86360 : Type'} : ((term266 _86360) = (term267 _86360)) = ((term264 _86360) = (term285 _86360)).
Proof. exact (MK_COMB (@lem3292188 _86360) (@lem3292199 _86360)). Qed.
Lemma lem3292201 {_86360 : Type'} : (term264 _86360) = (term285 _86360).
Proof. exact (EQ_MP (@lem3292200 _86360) (@lem3292178 _86360)). Qed.
Lemma lem3292246 {_86360 : Type'} : (term261 _86360) = (term261 _86360).
Proof. exact (eq_refl (term261 _86360)). Qed.
Lemma lem3292247 {_86360 : Type'} : (term265 _86360) = (term286 _86360).
Proof. exact (MK_COMB (@lem3292246 _86360) (@lem3292201 _86360)). Qed.
Lemma lem3292250 {_86360 : Type'} : (term244 _86360) = (term286 _86360).
Proof. exact (TRANS (@lem3292148 _86360) (@lem3292247 _86360)). Qed.
Lemma lem3292251 {_86360 : Type'} : (term241 _86360) = (term241 _86360).
Proof. exact (eq_refl (term241 _86360)). Qed.
Lemma lem3292252 {_86360 : Type'} : (term245 _86360) = (term287 _86360).
Proof. exact (MK_COMB (@lem3292251 _86360) (@lem3292250 _86360)). Qed.
Lemma lem3292255 {_86360 : Type'} : (term225 _86360) = (term287 _86360).
Proof. exact (TRANS (@lem3292103 _86360) (@lem3292252 _86360)). Qed.
Lemma lem3292260 {_86360 : Type'} : (term224 _86360) = (term287 _86360).
Proof. exact (TRANS (@lem3292076 _86360) (@lem3292255 _86360)). Qed.
Lemma lem3292277 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : ((term66 _86360 p q x) = (term29 _86360 p q x)) = ((term66 _86360 p q x) = (term29 _86360 p q x)).
Proof. exact (eq_refl ((term66 _86360 p q x) = (term29 _86360 p q x))). Qed.
Lemma lem3292278 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term70 _86360 p q) = (term70 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3292277 _86360 p q x)). Qed.
Lemma lem3292279 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3292280 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term71 _86360 p q) = (term71 _86360 p q).
Proof. exact (MK_COMB (@lem3292279 _86360) (@lem3292278 _86360 p q)). Qed.
Lemma lem3292281 {_86360 : Type'} (q : _86360 -> Prop) : (term203 _86360 q) = (term203 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292280 _86360 p q)). Qed.
Lemma lem3292282 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292283 {_86360 : Type'} (q : _86360 -> Prop) : (term218 _86360 q) = (term218 _86360 q).
Proof. exact (MK_COMB (@lem3292282 _86360) (@lem3292281 _86360 q)). Qed.
Lemma lem3292284 {_86360 : Type'} : (term269 _86360) = (term269 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292283 _86360 q)). Qed.
Lemma lem3292285 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292286 {_86360 : Type'} : (term284 _86360) = (term284 _86360).
Proof. exact (MK_COMB (@lem3292285 _86360) (@lem3292284 _86360)). Qed.
Lemma lem3292307 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : ((term45 _86360 p q r x) = (term45 _86360 q p r x)) = ((term45 _86360 p q r x) = (term45 _86360 q p r x)).
Proof. exact (eq_refl ((term45 _86360 p q r x) = (term45 _86360 q p r x))). Qed.
Lemma lem3292308 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term53 _86360 q p r) = (term53 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3292307 _86360 q p r x)). Qed.
Lemma lem3292309 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3292310 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term54 _86360 q p r) = (term54 _86360 q p r).
Proof. exact (MK_COMB (@lem3292309 _86360) (@lem3292308 _86360 q p r)). Qed.
Lemma lem3292311 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term135 _86360 q p) = (term135 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3292310 _86360 q p r)). Qed.
Lemma lem3292312 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292313 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term146 _86360 q p) = (term146 _86360 q p).
Proof. exact (MK_COMB (@lem3292312 _86360) (@lem3292311 _86360 q p)). Qed.
Lemma lem3292314 {_86360 : Type'} (q : _86360 -> Prop) : (term202 _86360 q) = (term202 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292313 _86360 q p)). Qed.
Lemma lem3292315 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292316 {_86360 : Type'} (q : _86360 -> Prop) : (term213 _86360 q) = (term213 _86360 q).
Proof. exact (MK_COMB (@lem3292315 _86360) (@lem3292314 _86360 q)). Qed.
Lemma lem3292317 {_86360 : Type'} : (term268 _86360) = (term268 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292316 _86360 q)). Qed.
Lemma lem3292318 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292319 {_86360 : Type'} : (term279 _86360) = (term279 _86360).
Proof. exact (MK_COMB (@lem3292318 _86360) (@lem3292317 _86360)). Qed.
Lemma lem3292320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292321 {_86360 : Type'} : (term281 _86360) = (term281 _86360).
Proof. exact (MK_COMB (@lem3292320) (@lem3292319 _86360)). Qed.
Lemma lem3292322 {_86360 : Type'} : (term285 _86360) = (term285 _86360).
Proof. exact (MK_COMB (@lem3292321 _86360) (@lem3292286 _86360)). Qed.
Lemma lem3292343 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : ((term40 _86360 p q r x) = (term45 _86360 p q r x)) = ((term40 _86360 p q r x) = (term45 _86360 p q r x)).
Proof. exact (eq_refl ((term40 _86360 p q r x) = (term45 _86360 p q r x))). Qed.
Lemma lem3292344 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term47 _86360 p q r) = (term47 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3292343 _86360 p q r x)). Qed.
Lemma lem3292345 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3292346 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term48 _86360 p q r) = (term48 _86360 p q r).
Proof. exact (MK_COMB (@lem3292345 _86360) (@lem3292344 _86360 p q r)). Qed.
Lemma lem3292347 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term115 _86360 p q) = (term115 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3292346 _86360 p q r)). Qed.
Lemma lem3292348 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292349 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term126 _86360 p q) = (term126 _86360 p q).
Proof. exact (MK_COMB (@lem3292348 _86360) (@lem3292347 _86360 p q)). Qed.
Lemma lem3292350 {_86360 : Type'} (q : _86360 -> Prop) : (term182 _86360 q) = (term182 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292349 _86360 p q)). Qed.
Lemma lem3292351 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292352 {_86360 : Type'} (q : _86360 -> Prop) : (term193 _86360 q) = (term193 _86360 q).
Proof. exact (MK_COMB (@lem3292351 _86360) (@lem3292350 _86360 q)). Qed.
Lemma lem3292353 {_86360 : Type'} : (term248 _86360) = (term248 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292352 _86360 q)). Qed.
Lemma lem3292354 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292355 {_86360 : Type'} : (term259 _86360) = (term259 _86360).
Proof. exact (MK_COMB (@lem3292354 _86360) (@lem3292353 _86360)). Qed.
Lemma lem3292356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292357 {_86360 : Type'} : (term261 _86360) = (term261 _86360).
Proof. exact (MK_COMB (@lem3292356) (@lem3292355 _86360)). Qed.
Lemma lem3292358 {_86360 : Type'} : (term286 _86360) = (term286 _86360).
Proof. exact (MK_COMB (@lem3292357 _86360) (@lem3292322 _86360)). Qed.
Lemma lem3292371 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : ((term29 _86360 p q x) = (term29 _86360 q p x)) = ((term29 _86360 p q x) = (term29 _86360 q p x)).
Proof. exact (eq_refl ((term29 _86360 p q x) = (term29 _86360 q p x))). Qed.
Lemma lem3292372 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term33 _86360 q p) = (term33 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3292371 _86360 q p x)). Qed.
Lemma lem3292373 {_86360 : Type'} : (@all _86360) = (@all _86360).
Proof. exact (eq_refl (@all _86360)). Qed.
Lemma lem3292374 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term34 _86360 q p) = (term34 _86360 q p).
Proof. exact (MK_COMB (@lem3292373 _86360) (@lem3292372 _86360 q p)). Qed.
Lemma lem3292375 {_86360 : Type'} (q : _86360 -> Prop) : (term162 _86360 q) = (term162 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292374 _86360 q p)). Qed.
Lemma lem3292376 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292377 {_86360 : Type'} (q : _86360 -> Prop) : (term173 _86360 q) = (term173 _86360 q).
Proof. exact (MK_COMB (@lem3292376 _86360) (@lem3292375 _86360 q)). Qed.
Lemma lem3292378 {_86360 : Type'} : (term228 _86360) = (term228 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292377 _86360 q)). Qed.
Lemma lem3292379 {_86360 : Type'} : (@all (_86360 -> Prop)) = (@all (_86360 -> Prop)).
Proof. exact (eq_refl (@all (_86360 -> Prop))). Qed.
Lemma lem3292380 {_86360 : Type'} : (term239 _86360) = (term239 _86360).
Proof. exact (MK_COMB (@lem3292379 _86360) (@lem3292378 _86360)). Qed.
Lemma lem3292381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292382 {_86360 : Type'} : (term241 _86360) = (term241 _86360).
Proof. exact (MK_COMB (@lem3292381) (@lem3292380 _86360)). Qed.
Lemma lem3292383 {_86360 : Type'} : (term287 _86360) = (term287 _86360).
Proof. exact (MK_COMB (@lem3292382 _86360) (@lem3292358 _86360)). Qed.
Lemma lem3292502 {_86360 : Type'} : (term224 _86360) = (term287 _86360).
Proof. exact (TRANS (@lem3292260 _86360) (@lem3292383 _86360)). Qed.
Lemma lem3292503 {_86360 : Type'} : (term287 _86360) = (term224 _86360).
Proof. exact (SYM (@lem3292502 _86360)). Qed.
Lemma lem3292505 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3292506 {_86360 : Type'} : (term287 _86360) = (term288 _86360).
Proof. exact (@lem3292505 (term287 _86360)). Qed.
Lemma lem3292507 {_86360 : Type'} : (term288 _86360) = (term287 _86360).
Proof. exact (SYM (@lem3292506 _86360)). Qed.
Lemma lem3292508 {_86360 : Type'} (h1 : term289 _86360) : term289 _86360.
Proof. exact (h1). Qed.
Lemma lem3292517 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term290 _86360 p q x) = (term291 _86360 p q x).
Proof. exact (@lem17045 (p x) (q x)). Qed.
Lemma lem3292529 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term290 _86360 q p x) = (term291 _86360 q p x).
Proof. exact (@lem17045 (q x) (p x)). Qed.
Lemma lem3292532 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term29 _86360 q p x) = (term29 _86360 q p x).
Proof. exact (eq_refl (term29 _86360 q p x)). Qed.
Lemma lem3292533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292534 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term292 _86360 p q x) = (term293 _86360 p q x).
Proof. exact (MK_COMB (@lem3292533) (@lem3292517 _86360 p q x)). Qed.
Lemma lem3292535 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term294 _86360 q p x) = (term295 _86360 q p x).
Proof. exact (MK_COMB (@lem3292534 _86360 p q x) (@lem3292532 _86360 q p x)). Qed.
Lemma lem3292537 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term39 _86360 p q x) = (term39 _86360 p q x).
Proof. exact (eq_refl (term39 _86360 p q x)). Qed.
Lemma lem3292538 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term296 _86360 q p x) = (term297 _86360 q p x).
Proof. exact (MK_COMB (@lem3292537 _86360 p q x) (@lem3292529 _86360 q p x)). Qed.
Lemma lem3292539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292540 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term298 _86360 q p x) = (term299 _86360 q p x).
Proof. exact (MK_COMB (@lem3292539) (@lem3292538 _86360 q p x)). Qed.
Lemma lem3292541 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term300 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (MK_COMB (@lem3292540 _86360 q p x) (@lem3292535 _86360 q p x)). Qed.
Lemma lem3292542 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term302 _86360 q p x) = (term300 _86360 q p x).
Proof. exact (@lem17646 (term29 _86360 p q x) (term29 _86360 q p x)). Qed.
Lemma lem3292543 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term302 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (TRANS (@lem3292542 _86360 q p x) (@lem3292541 _86360 q p x)). Qed.
Lemma lem3292544 {_86360 : Type'} (P : _86360 -> Prop) : (term303 _86360 P) = (term304 _86360 P).
Proof. exact (@lem18392 _86360 P). Qed.
Lemma lem3292545 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term305 _86360 q p) = (term306 _86360 q p).
Proof. exact (@lem3292544 _86360 (term33 _86360 q p)). Qed.
Lemma lem3292546 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term307 _86360 q p x) = ((term29 _86360 p q x) = (term29 _86360 q p x)).
Proof. exact (eq_refl (term307 _86360 q p x)). Qed.
Lemma lem3292547 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292548 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term308 _86360 q p x) = (term302 _86360 q p x).
Proof. exact (MK_COMB (@lem3292547) (@lem3292546 _86360 q p x)). Qed.
Lemma lem3292549 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term308 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (TRANS (@lem3292548 _86360 q p x) (@lem3292543 _86360 q p x)). Qed.
Lemma lem3292550 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term309 _86360 q p) = (term310 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3292549 _86360 q p x)). Qed.
Lemma lem3292551 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292552 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term306 _86360 q p) = (term311 _86360 q p).
Proof. exact (MK_COMB (@lem3292551 _86360) (@lem3292550 _86360 q p)). Qed.
Lemma lem3292553 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term305 _86360 q p) = (term311 _86360 q p).
Proof. exact (TRANS (@lem3292545 _86360 q p) (@lem3292552 _86360 q p)). Qed.
Lemma lem3292554 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292555 {_86360 : Type'} (q : _86360 -> Prop) : (term314 _86360 q) = (term315 _86360 q).
Proof. exact (@lem3292554 _86360 (term162 _86360 q)). Qed.
Lemma lem3292556 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term164 _86360 q p) = (term34 _86360 q p).
Proof. exact (eq_refl (term164 _86360 q p)). Qed.
Lemma lem3292557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292558 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term316 _86360 q p) = (term305 _86360 q p).
Proof. exact (MK_COMB (@lem3292557) (@lem3292556 _86360 q p)). Qed.
Lemma lem3292559 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term316 _86360 q p) = (term311 _86360 q p).
Proof. exact (TRANS (@lem3292558 _86360 q p) (@lem3292553 _86360 q p)). Qed.
Lemma lem3292560 {_86360 : Type'} (q : _86360 -> Prop) : (term317 _86360 q) = (term318 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292559 _86360 q p)). Qed.
Lemma lem3292561 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292562 {_86360 : Type'} (q : _86360 -> Prop) : (term315 _86360 q) = (term319 _86360 q).
Proof. exact (MK_COMB (@lem3292561 _86360) (@lem3292560 _86360 q)). Qed.
Lemma lem3292563 {_86360 : Type'} (q : _86360 -> Prop) : (term314 _86360 q) = (term319 _86360 q).
Proof. exact (TRANS (@lem3292555 _86360 q) (@lem3292562 _86360 q)). Qed.
Lemma lem3292564 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292565 {_86360 : Type'} : (term320 _86360) = (term321 _86360).
Proof. exact (@lem3292564 _86360 (term228 _86360)). Qed.
Lemma lem3292566 {_86360 : Type'} (q : _86360 -> Prop) : (term230 _86360 q) = (term173 _86360 q).
Proof. exact (eq_refl (term230 _86360 q)). Qed.
Lemma lem3292567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292568 {_86360 : Type'} (q : _86360 -> Prop) : (term322 _86360 q) = (term314 _86360 q).
Proof. exact (MK_COMB (@lem3292567) (@lem3292566 _86360 q)). Qed.
Lemma lem3292569 {_86360 : Type'} (q : _86360 -> Prop) : (term322 _86360 q) = (term319 _86360 q).
Proof. exact (TRANS (@lem3292568 _86360 q) (@lem3292563 _86360 q)). Qed.
Lemma lem3292570 {_86360 : Type'} : (term323 _86360) = (term324 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292569 _86360 q)). Qed.
Lemma lem3292571 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292572 {_86360 : Type'} : (term321 _86360) = (term325 _86360).
Proof. exact (MK_COMB (@lem3292571 _86360) (@lem3292570 _86360)). Qed.
Lemma lem3292573 {_86360 : Type'} : (term320 _86360) = (term325 _86360).
Proof. exact (TRANS (@lem3292565 _86360) (@lem3292572 _86360)). Qed.
Lemma lem3292582 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term290 _86360 p q x) = (term291 _86360 p q x).
Proof. exact (@lem17045 (p x) (q x)). Qed.
Lemma lem3292586 {_86360 : Type'} (r : _86360 -> Prop) (x : _86360) : (term326 _86360 r x) = (term326 _86360 r x).
Proof. exact (eq_refl (term326 _86360 r x)). Qed.
Lemma lem3292588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292589 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term327 _86360 p q x) = (term328 _86360 p q x).
Proof. exact (MK_COMB (@lem3292588) (@lem3292582 _86360 p q x)). Qed.
Lemma lem3292590 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term329 _86360 p q r x) = (term330 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292589 _86360 p q x) (@lem3292586 _86360 r x)). Qed.
Lemma lem3292591 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term331 _86360 p q r x) = (term329 _86360 p q r x).
Proof. exact (@lem17045 (term29 _86360 p q x) (r x)). Qed.
Lemma lem3292592 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term331 _86360 p q r x) = (term330 _86360 p q r x).
Proof. exact (TRANS (@lem3292591 _86360 p q r x) (@lem3292590 _86360 p q r x)). Qed.
Lemma lem3292606 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term290 _86360 q r x) = (term291 _86360 q r x).
Proof. exact (@lem17045 (q x) (r x)). Qed.
Lemma lem3292611 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term332 _86360 p x) = (term332 _86360 p x).
Proof. exact (eq_refl (term332 _86360 p x)). Qed.
Lemma lem3292612 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term333 _86360 p q r x) = (term334 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292611 _86360 p x) (@lem3292606 _86360 q r x)). Qed.
Lemma lem3292613 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term335 _86360 p q r x) = (term333 _86360 p q r x).
Proof. exact (@lem17045 (p x) (term29 _86360 q r x)). Qed.
Lemma lem3292614 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term335 _86360 p q r x) = (term334 _86360 p q r x).
Proof. exact (TRANS (@lem3292613 _86360 p q r x) (@lem3292612 _86360 p q r x)). Qed.
Lemma lem3292617 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term45 _86360 p q r x) = (term45 _86360 p q r x).
Proof. exact (eq_refl (term45 _86360 p q r x)). Qed.
Lemma lem3292618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292619 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term336 _86360 p q r x) = (term337 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292618) (@lem3292592 _86360 p q r x)). Qed.
Lemma lem3292620 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term338 _86360 p q r x) = (term339 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292619 _86360 p q r x) (@lem3292617 _86360 p q r x)). Qed.
Lemma lem3292622 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term340 _86360 p q r x) = (term340 _86360 p q r x).
Proof. exact (eq_refl (term340 _86360 p q r x)). Qed.
Lemma lem3292623 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term341 _86360 p q r x) = (term342 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292622 _86360 p q r x) (@lem3292614 _86360 p q r x)). Qed.
Lemma lem3292624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292625 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term343 _86360 p q r x) = (term344 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292624) (@lem3292623 _86360 p q r x)). Qed.
Lemma lem3292626 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term345 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292625 _86360 p q r x) (@lem3292620 _86360 p q r x)). Qed.
Lemma lem3292627 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term347 _86360 p q r x) = (term345 _86360 p q r x).
Proof. exact (@lem17646 (term40 _86360 p q r x) (term45 _86360 p q r x)). Qed.
Lemma lem3292628 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term347 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (TRANS (@lem3292627 _86360 p q r x) (@lem3292626 _86360 p q r x)). Qed.
Lemma lem3292629 {_86360 : Type'} (P : _86360 -> Prop) : (term303 _86360 P) = (term304 _86360 P).
Proof. exact (@lem18392 _86360 P). Qed.
Lemma lem3292630 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term348 _86360 p q r) = (term349 _86360 p q r).
Proof. exact (@lem3292629 _86360 (term47 _86360 p q r)). Qed.
Lemma lem3292631 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term350 _86360 p q r x) = ((term40 _86360 p q r x) = (term45 _86360 p q r x)).
Proof. exact (eq_refl (term350 _86360 p q r x)). Qed.
Lemma lem3292632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292633 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term351 _86360 p q r x) = (term347 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292632) (@lem3292631 _86360 p q r x)). Qed.
Lemma lem3292634 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term351 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (TRANS (@lem3292633 _86360 p q r x) (@lem3292628 _86360 p q r x)). Qed.
Lemma lem3292635 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term352 _86360 p q r) = (term353 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3292634 _86360 p q r x)). Qed.
Lemma lem3292636 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292637 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term349 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (MK_COMB (@lem3292636 _86360) (@lem3292635 _86360 p q r)). Qed.
Lemma lem3292638 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term348 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (TRANS (@lem3292630 _86360 p q r) (@lem3292637 _86360 p q r)). Qed.
Lemma lem3292639 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292640 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term355 _86360 p q) = (term356 _86360 p q).
Proof. exact (@lem3292639 _86360 (term115 _86360 p q)). Qed.
Lemma lem3292641 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term117 _86360 p q r) = (term48 _86360 p q r).
Proof. exact (eq_refl (term117 _86360 p q r)). Qed.
Lemma lem3292642 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292643 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term357 _86360 p q r) = (term348 _86360 p q r).
Proof. exact (MK_COMB (@lem3292642) (@lem3292641 _86360 p q r)). Qed.
Lemma lem3292644 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term357 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (TRANS (@lem3292643 _86360 p q r) (@lem3292638 _86360 p q r)). Qed.
Lemma lem3292645 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term358 _86360 p q) = (term359 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3292644 _86360 p q r)). Qed.
Lemma lem3292646 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292647 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term356 _86360 p q) = (term360 _86360 p q).
Proof. exact (MK_COMB (@lem3292646 _86360) (@lem3292645 _86360 p q)). Qed.
Lemma lem3292648 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term355 _86360 p q) = (term360 _86360 p q).
Proof. exact (TRANS (@lem3292640 _86360 p q) (@lem3292647 _86360 p q)). Qed.
Lemma lem3292649 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292650 {_86360 : Type'} (q : _86360 -> Prop) : (term361 _86360 q) = (term362 _86360 q).
Proof. exact (@lem3292649 _86360 (term182 _86360 q)). Qed.
Lemma lem3292651 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term184 _86360 q p) = (term126 _86360 p q).
Proof. exact (eq_refl (term184 _86360 q p)). Qed.
Lemma lem3292652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292653 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term363 _86360 q p) = (term355 _86360 p q).
Proof. exact (MK_COMB (@lem3292652) (@lem3292651 _86360 p q)). Qed.
Lemma lem3292654 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term363 _86360 q p) = (term360 _86360 p q).
Proof. exact (TRANS (@lem3292653 _86360 p q) (@lem3292648 _86360 p q)). Qed.
Lemma lem3292655 {_86360 : Type'} (q : _86360 -> Prop) : (term364 _86360 q) = (term365 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292654 _86360 p q)). Qed.
Lemma lem3292656 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292657 {_86360 : Type'} (q : _86360 -> Prop) : (term362 _86360 q) = (term366 _86360 q).
Proof. exact (MK_COMB (@lem3292656 _86360) (@lem3292655 _86360 q)). Qed.
Lemma lem3292658 {_86360 : Type'} (q : _86360 -> Prop) : (term361 _86360 q) = (term366 _86360 q).
Proof. exact (TRANS (@lem3292650 _86360 q) (@lem3292657 _86360 q)). Qed.
Lemma lem3292659 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292660 {_86360 : Type'} : (term367 _86360) = (term368 _86360).
Proof. exact (@lem3292659 _86360 (term248 _86360)). Qed.
Lemma lem3292661 {_86360 : Type'} (q : _86360 -> Prop) : (term250 _86360 q) = (term193 _86360 q).
Proof. exact (eq_refl (term250 _86360 q)). Qed.
Lemma lem3292662 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292663 {_86360 : Type'} (q : _86360 -> Prop) : (term369 _86360 q) = (term361 _86360 q).
Proof. exact (MK_COMB (@lem3292662) (@lem3292661 _86360 q)). Qed.
Lemma lem3292664 {_86360 : Type'} (q : _86360 -> Prop) : (term369 _86360 q) = (term366 _86360 q).
Proof. exact (TRANS (@lem3292663 _86360 q) (@lem3292658 _86360 q)). Qed.
Lemma lem3292665 {_86360 : Type'} : (term370 _86360) = (term371 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292664 _86360 q)). Qed.
Lemma lem3292666 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292667 {_86360 : Type'} : (term368 _86360) = (term372 _86360).
Proof. exact (MK_COMB (@lem3292666 _86360) (@lem3292665 _86360)). Qed.
Lemma lem3292668 {_86360 : Type'} : (term367 _86360) = (term372 _86360).
Proof. exact (TRANS (@lem3292660 _86360) (@lem3292667 _86360)). Qed.
Lemma lem3292679 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term290 _86360 q r x) = (term291 _86360 q r x).
Proof. exact (@lem17045 (q x) (r x)). Qed.
Lemma lem3292684 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term332 _86360 p x) = (term332 _86360 p x).
Proof. exact (eq_refl (term332 _86360 p x)). Qed.
Lemma lem3292685 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term333 _86360 p q r x) = (term334 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292684 _86360 p x) (@lem3292679 _86360 q r x)). Qed.
Lemma lem3292686 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term335 _86360 p q r x) = (term333 _86360 p q r x).
Proof. exact (@lem17045 (p x) (term29 _86360 q r x)). Qed.
Lemma lem3292687 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term335 _86360 p q r x) = (term334 _86360 p q r x).
Proof. exact (TRANS (@lem3292686 _86360 p q r x) (@lem3292685 _86360 p q r x)). Qed.
Lemma lem3292701 {_86360 : Type'} (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term290 _86360 p r x) = (term291 _86360 p r x).
Proof. exact (@lem17045 (p x) (r x)). Qed.
Lemma lem3292706 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term332 _86360 q x) = (term332 _86360 q x).
Proof. exact (eq_refl (term332 _86360 q x)). Qed.
Lemma lem3292707 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term333 _86360 q p r x) = (term334 _86360 q p r x).
Proof. exact (MK_COMB (@lem3292706 _86360 q x) (@lem3292701 _86360 p r x)). Qed.
Lemma lem3292708 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term335 _86360 q p r x) = (term333 _86360 q p r x).
Proof. exact (@lem17045 (q x) (term29 _86360 p r x)). Qed.
Lemma lem3292709 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term335 _86360 q p r x) = (term334 _86360 q p r x).
Proof. exact (TRANS (@lem3292708 _86360 q p r x) (@lem3292707 _86360 q p r x)). Qed.
Lemma lem3292712 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term45 _86360 q p r x) = (term45 _86360 q p r x).
Proof. exact (eq_refl (term45 _86360 q p r x)). Qed.
Lemma lem3292713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292714 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term373 _86360 p q r x) = (term374 _86360 p q r x).
Proof. exact (MK_COMB (@lem3292713) (@lem3292687 _86360 p q r x)). Qed.
Lemma lem3292715 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term375 _86360 q p r x) = (term376 _86360 q p r x).
Proof. exact (MK_COMB (@lem3292714 _86360 p q r x) (@lem3292712 _86360 q p r x)). Qed.
Lemma lem3292717 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term377 _86360 p q r x) = (term377 _86360 p q r x).
Proof. exact (eq_refl (term377 _86360 p q r x)). Qed.
Lemma lem3292718 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term378 _86360 q p r x) = (term379 _86360 q p r x).
Proof. exact (MK_COMB (@lem3292717 _86360 p q r x) (@lem3292709 _86360 q p r x)). Qed.
Lemma lem3292719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292720 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term380 _86360 q p r x) = (term381 _86360 q p r x).
Proof. exact (MK_COMB (@lem3292719) (@lem3292718 _86360 q p r x)). Qed.
Lemma lem3292721 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term382 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (MK_COMB (@lem3292720 _86360 q p r x) (@lem3292715 _86360 q p r x)). Qed.
Lemma lem3292722 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term384 _86360 q p r x) = (term382 _86360 q p r x).
Proof. exact (@lem17646 (term45 _86360 p q r x) (term45 _86360 q p r x)). Qed.
Lemma lem3292723 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term384 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (TRANS (@lem3292722 _86360 q p r x) (@lem3292721 _86360 q p r x)). Qed.
Lemma lem3292724 {_86360 : Type'} (P : _86360 -> Prop) : (term303 _86360 P) = (term304 _86360 P).
Proof. exact (@lem18392 _86360 P). Qed.
Lemma lem3292725 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term385 _86360 q p r) = (term386 _86360 q p r).
Proof. exact (@lem3292724 _86360 (term53 _86360 q p r)). Qed.
Lemma lem3292726 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term387 _86360 q p r x) = ((term45 _86360 p q r x) = (term45 _86360 q p r x)).
Proof. exact (eq_refl (term387 _86360 q p r x)). Qed.
Lemma lem3292727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292728 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term388 _86360 q p r x) = (term384 _86360 q p r x).
Proof. exact (MK_COMB (@lem3292727) (@lem3292726 _86360 q p r x)). Qed.
Lemma lem3292729 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term388 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (TRANS (@lem3292728 _86360 q p r x) (@lem3292723 _86360 q p r x)). Qed.
Lemma lem3292730 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term389 _86360 q p r) = (term390 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3292729 _86360 q p r x)). Qed.
Lemma lem3292731 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292732 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term386 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (MK_COMB (@lem3292731 _86360) (@lem3292730 _86360 q p r)). Qed.
Lemma lem3292733 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term385 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (TRANS (@lem3292725 _86360 q p r) (@lem3292732 _86360 q p r)). Qed.
Lemma lem3292734 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292735 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term392 _86360 q p) = (term393 _86360 q p).
Proof. exact (@lem3292734 _86360 (term135 _86360 q p)). Qed.
Lemma lem3292736 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term137 _86360 q p r) = (term54 _86360 q p r).
Proof. exact (eq_refl (term137 _86360 q p r)). Qed.
Lemma lem3292737 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292738 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term394 _86360 q p r) = (term385 _86360 q p r).
Proof. exact (MK_COMB (@lem3292737) (@lem3292736 _86360 q p r)). Qed.
Lemma lem3292739 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term394 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (TRANS (@lem3292738 _86360 q p r) (@lem3292733 _86360 q p r)). Qed.
Lemma lem3292740 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term395 _86360 q p) = (term396 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3292739 _86360 q p r)). Qed.
Lemma lem3292741 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292742 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term393 _86360 q p) = (term397 _86360 q p).
Proof. exact (MK_COMB (@lem3292741 _86360) (@lem3292740 _86360 q p)). Qed.
Lemma lem3292743 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term392 _86360 q p) = (term397 _86360 q p).
Proof. exact (TRANS (@lem3292735 _86360 q p) (@lem3292742 _86360 q p)). Qed.
Lemma lem3292744 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292745 {_86360 : Type'} (q : _86360 -> Prop) : (term398 _86360 q) = (term399 _86360 q).
Proof. exact (@lem3292744 _86360 (term202 _86360 q)). Qed.
Lemma lem3292746 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term204 _86360 q p) = (term146 _86360 q p).
Proof. exact (eq_refl (term204 _86360 q p)). Qed.
Lemma lem3292747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292748 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term400 _86360 q p) = (term392 _86360 q p).
Proof. exact (MK_COMB (@lem3292747) (@lem3292746 _86360 q p)). Qed.
Lemma lem3292749 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term400 _86360 q p) = (term397 _86360 q p).
Proof. exact (TRANS (@lem3292748 _86360 q p) (@lem3292743 _86360 q p)). Qed.
Lemma lem3292750 {_86360 : Type'} (q : _86360 -> Prop) : (term401 _86360 q) = (term402 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292749 _86360 q p)). Qed.
Lemma lem3292751 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292752 {_86360 : Type'} (q : _86360 -> Prop) : (term399 _86360 q) = (term403 _86360 q).
Proof. exact (MK_COMB (@lem3292751 _86360) (@lem3292750 _86360 q)). Qed.
Lemma lem3292753 {_86360 : Type'} (q : _86360 -> Prop) : (term398 _86360 q) = (term403 _86360 q).
Proof. exact (TRANS (@lem3292745 _86360 q) (@lem3292752 _86360 q)). Qed.
Lemma lem3292754 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292755 {_86360 : Type'} : (term404 _86360) = (term405 _86360).
Proof. exact (@lem3292754 _86360 (term268 _86360)). Qed.
Lemma lem3292756 {_86360 : Type'} (q : _86360 -> Prop) : (term270 _86360 q) = (term213 _86360 q).
Proof. exact (eq_refl (term270 _86360 q)). Qed.
Lemma lem3292757 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292758 {_86360 : Type'} (q : _86360 -> Prop) : (term406 _86360 q) = (term398 _86360 q).
Proof. exact (MK_COMB (@lem3292757) (@lem3292756 _86360 q)). Qed.
Lemma lem3292759 {_86360 : Type'} (q : _86360 -> Prop) : (term406 _86360 q) = (term403 _86360 q).
Proof. exact (TRANS (@lem3292758 _86360 q) (@lem3292753 _86360 q)). Qed.
Lemma lem3292760 {_86360 : Type'} : (term407 _86360) = (term408 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292759 _86360 q)). Qed.
Lemma lem3292761 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292762 {_86360 : Type'} : (term405 _86360) = (term409 _86360).
Proof. exact (MK_COMB (@lem3292761 _86360) (@lem3292760 _86360)). Qed.
Lemma lem3292763 {_86360 : Type'} : (term404 _86360) = (term409 _86360).
Proof. exact (TRANS (@lem3292755 _86360) (@lem3292762 _86360)). Qed.
Lemma lem3292774 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term290 _86360 p q x) = (term291 _86360 p q x).
Proof. exact (@lem17045 (p x) (q x)). Qed.
Lemma lem3292779 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term332 _86360 p x) = (term332 _86360 p x).
Proof. exact (eq_refl (term332 _86360 p x)). Qed.
Lemma lem3292780 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term410 _86360 p q x) = (term411 _86360 p q x).
Proof. exact (MK_COMB (@lem3292779 _86360 p x) (@lem3292774 _86360 p q x)). Qed.
Lemma lem3292781 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term412 _86360 p q x) = (term410 _86360 p q x).
Proof. exact (@lem17045 (p x) (term29 _86360 p q x)). Qed.
Lemma lem3292782 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term412 _86360 p q x) = (term411 _86360 p q x).
Proof. exact (TRANS (@lem3292781 _86360 p q x) (@lem3292780 _86360 p q x)). Qed.
Lemma lem3292794 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term290 _86360 p q x) = (term291 _86360 p q x).
Proof. exact (@lem17045 (p x) (q x)). Qed.
Lemma lem3292797 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term29 _86360 p q x) = (term29 _86360 p q x).
Proof. exact (eq_refl (term29 _86360 p q x)). Qed.
Lemma lem3292798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3292799 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term413 _86360 p q x) = (term414 _86360 p q x).
Proof. exact (MK_COMB (@lem3292798) (@lem3292782 _86360 p q x)). Qed.
Lemma lem3292800 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term415 _86360 p q x) = (term416 _86360 p q x).
Proof. exact (MK_COMB (@lem3292799 _86360 p q x) (@lem3292797 _86360 p q x)). Qed.
Lemma lem3292802 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term417 _86360 p q x) = (term417 _86360 p q x).
Proof. exact (eq_refl (term417 _86360 p q x)). Qed.
Lemma lem3292803 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term418 _86360 p q x) = (term419 _86360 p q x).
Proof. exact (MK_COMB (@lem3292802 _86360 p q x) (@lem3292794 _86360 p q x)). Qed.
Lemma lem3292804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292805 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term420 _86360 p q x) = (term421 _86360 p q x).
Proof. exact (MK_COMB (@lem3292804) (@lem3292803 _86360 p q x)). Qed.
Lemma lem3292806 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term422 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (MK_COMB (@lem3292805 _86360 p q x) (@lem3292800 _86360 p q x)). Qed.
Lemma lem3292807 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term424 _86360 p q x) = (term422 _86360 p q x).
Proof. exact (@lem17646 (term66 _86360 p q x) (term29 _86360 p q x)). Qed.
Lemma lem3292808 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term424 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (TRANS (@lem3292807 _86360 p q x) (@lem3292806 _86360 p q x)). Qed.
Lemma lem3292809 {_86360 : Type'} (P : _86360 -> Prop) : (term303 _86360 P) = (term304 _86360 P).
Proof. exact (@lem18392 _86360 P). Qed.
Lemma lem3292810 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term425 _86360 p q) = (term426 _86360 p q).
Proof. exact (@lem3292809 _86360 (term70 _86360 p q)). Qed.
Lemma lem3292811 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term427 _86360 p q x) = ((term66 _86360 p q x) = (term29 _86360 p q x)).
Proof. exact (eq_refl (term427 _86360 p q x)). Qed.
Lemma lem3292812 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292813 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term428 _86360 p q x) = (term424 _86360 p q x).
Proof. exact (MK_COMB (@lem3292812) (@lem3292811 _86360 p q x)). Qed.
Lemma lem3292814 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term428 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (TRANS (@lem3292813 _86360 p q x) (@lem3292808 _86360 p q x)). Qed.
Lemma lem3292815 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term429 _86360 p q) = (term430 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3292814 _86360 p q x)). Qed.
Lemma lem3292816 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292817 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term426 _86360 p q) = (term431 _86360 p q).
Proof. exact (MK_COMB (@lem3292816 _86360) (@lem3292815 _86360 p q)). Qed.
Lemma lem3292818 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term425 _86360 p q) = (term431 _86360 p q).
Proof. exact (TRANS (@lem3292810 _86360 p q) (@lem3292817 _86360 p q)). Qed.
Lemma lem3292819 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292820 {_86360 : Type'} (q : _86360 -> Prop) : (term432 _86360 q) = (term433 _86360 q).
Proof. exact (@lem3292819 _86360 (term203 _86360 q)). Qed.
Lemma lem3292821 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term206 _86360 q p) = (term71 _86360 p q).
Proof. exact (eq_refl (term206 _86360 q p)). Qed.
Lemma lem3292822 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292823 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term434 _86360 q p) = (term425 _86360 p q).
Proof. exact (MK_COMB (@lem3292822) (@lem3292821 _86360 p q)). Qed.
Lemma lem3292824 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term434 _86360 q p) = (term431 _86360 p q).
Proof. exact (TRANS (@lem3292823 _86360 p q) (@lem3292818 _86360 p q)). Qed.
Lemma lem3292825 {_86360 : Type'} (q : _86360 -> Prop) : (term435 _86360 q) = (term436 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292824 _86360 p q)). Qed.
Lemma lem3292826 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292827 {_86360 : Type'} (q : _86360 -> Prop) : (term433 _86360 q) = (term437 _86360 q).
Proof. exact (MK_COMB (@lem3292826 _86360) (@lem3292825 _86360 q)). Qed.
Lemma lem3292828 {_86360 : Type'} (q : _86360 -> Prop) : (term432 _86360 q) = (term437 _86360 q).
Proof. exact (TRANS (@lem3292820 _86360 q) (@lem3292827 _86360 q)). Qed.
Lemma lem3292829 {_86360 : Type'} (P : type686 _86360) : (term312 _86360 P) = (term313 _86360 P).
Proof. exact (@lem18392 (_86360 -> Prop) P). Qed.
Lemma lem3292830 {_86360 : Type'} : (term438 _86360) = (term439 _86360).
Proof. exact (@lem3292829 _86360 (term269 _86360)). Qed.
Lemma lem3292831 {_86360 : Type'} (q : _86360 -> Prop) : (term272 _86360 q) = (term218 _86360 q).
Proof. exact (eq_refl (term272 _86360 q)). Qed.
Lemma lem3292832 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3292833 {_86360 : Type'} (q : _86360 -> Prop) : (term440 _86360 q) = (term432 _86360 q).
Proof. exact (MK_COMB (@lem3292832) (@lem3292831 _86360 q)). Qed.
Lemma lem3292834 {_86360 : Type'} (q : _86360 -> Prop) : (term440 _86360 q) = (term437 _86360 q).
Proof. exact (TRANS (@lem3292833 _86360 q) (@lem3292828 _86360 q)). Qed.
Lemma lem3292835 {_86360 : Type'} : (term441 _86360) = (term442 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3292834 _86360 q)). Qed.
Lemma lem3292836 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292837 {_86360 : Type'} : (term439 _86360) = (term443 _86360).
Proof. exact (MK_COMB (@lem3292836 _86360) (@lem3292835 _86360)). Qed.
Lemma lem3292838 {_86360 : Type'} : (term438 _86360) = (term443 _86360).
Proof. exact (TRANS (@lem3292830 _86360) (@lem3292837 _86360)). Qed.
Lemma lem3292839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292840 {_86360 : Type'} : (term444 _86360) = (term445 _86360).
Proof. exact (MK_COMB (@lem3292839) (@lem3292763 _86360)). Qed.
Lemma lem3292841 {_86360 : Type'} : (term446 _86360) = (term447 _86360).
Proof. exact (MK_COMB (@lem3292840 _86360) (@lem3292838 _86360)). Qed.
Lemma lem3292842 {_86360 : Type'} : (term448 _86360) = (term446 _86360).
Proof. exact (@lem17045 (term279 _86360) (term284 _86360)). Qed.
Lemma lem3292843 {_86360 : Type'} : (term448 _86360) = (term447 _86360).
Proof. exact (TRANS (@lem3292842 _86360) (@lem3292841 _86360)). Qed.
Lemma lem3292844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292845 {_86360 : Type'} : (term449 _86360) = (term450 _86360).
Proof. exact (MK_COMB (@lem3292844) (@lem3292668 _86360)). Qed.
Lemma lem3292846 {_86360 : Type'} : (term451 _86360) = (term452 _86360).
Proof. exact (MK_COMB (@lem3292845 _86360) (@lem3292843 _86360)). Qed.
Lemma lem3292847 {_86360 : Type'} : (term453 _86360) = (term451 _86360).
Proof. exact (@lem17045 (term259 _86360) (term285 _86360)). Qed.
Lemma lem3292848 {_86360 : Type'} : (term453 _86360) = (term452 _86360).
Proof. exact (TRANS (@lem3292847 _86360) (@lem3292846 _86360)). Qed.
Lemma lem3292849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292850 {_86360 : Type'} : (term454 _86360) = (term455 _86360).
Proof. exact (MK_COMB (@lem3292849) (@lem3292573 _86360)). Qed.
Lemma lem3292851 {_86360 : Type'} : (term456 _86360) = (term457 _86360).
Proof. exact (MK_COMB (@lem3292850 _86360) (@lem3292848 _86360)). Qed.
Lemma lem3292852 {_86360 : Type'} : (term289 _86360) = (term456 _86360).
Proof. exact (@lem17045 (term239 _86360) (term286 _86360)). Qed.
Lemma lem3292853 {_86360 : Type'} : (term289 _86360) = (term457 _86360).
Proof. exact (TRANS (@lem3292852 _86360) (@lem3292851 _86360)). Qed.
Lemma lem3292863 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3292864 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term458 _86360 P Q) = (term459 _86360 P Q).
Proof. exact (@lem3292863 _86360 P Q). Qed.
Lemma lem3292865 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term460 _86360 q p) = (term461 _86360 q p).
Proof. exact (@lem3292864 _86360 (term462 _86360 q p) (term463 _86360 q p)). Qed.
Lemma lem3292866 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term464 _86360 q p x) = (term297 _86360 q p x).
Proof. exact (eq_refl (term464 _86360 q p x)). Qed.
Lemma lem3292867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292868 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term465 _86360 q p x) = (term299 _86360 q p x).
Proof. exact (MK_COMB (@lem3292867) (@lem3292866 _86360 q p x)). Qed.
Lemma lem3292869 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term466 _86360 q p x) = (term295 _86360 q p x).
Proof. exact (eq_refl (term466 _86360 q p x)). Qed.
Lemma lem3292870 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term467 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (MK_COMB (@lem3292868 _86360 q p x) (@lem3292869 _86360 q p x)). Qed.
Lemma lem3292871 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term468 _86360 q p) = (term310 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3292870 _86360 q p x)). Qed.
Lemma lem3292872 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292873 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term460 _86360 q p) = (term311 _86360 q p).
Proof. exact (MK_COMB (@lem3292872 _86360) (@lem3292871 _86360 q p)). Qed.
Lemma lem3292874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3292875 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term469 _86360 q p) = (term470 _86360 q p).
Proof. exact (MK_COMB (@lem3292874) (@lem3292873 _86360 q p)). Qed.
Lemma lem3292876 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term464 _86360 q p x) = (term297 _86360 q p x).
Proof. exact (eq_refl (term464 _86360 q p x)). Qed.
Lemma lem3292877 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term471 _86360 q p) = (term462 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3292876 _86360 q p x)). Qed.
Lemma lem3292878 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292879 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term472 _86360 q p) = (term473 _86360 q p).
Proof. exact (MK_COMB (@lem3292878 _86360) (@lem3292877 _86360 q p)). Qed.
Lemma lem3292880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292881 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term474 _86360 q p) = (term475 _86360 q p).
Proof. exact (MK_COMB (@lem3292880) (@lem3292879 _86360 q p)). Qed.
Lemma lem3292882 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term466 _86360 q p x) = (term295 _86360 q p x).
Proof. exact (eq_refl (term466 _86360 q p x)). Qed.
Lemma lem3292883 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term476 _86360 q p) = (term463 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3292882 _86360 q p x)). Qed.
Lemma lem3292884 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3292885 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term477 _86360 q p) = (term478 _86360 q p).
Proof. exact (MK_COMB (@lem3292884 _86360) (@lem3292883 _86360 q p)). Qed.
Lemma lem3292886 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term461 _86360 q p) = (term479 _86360 q p).
Proof. exact (MK_COMB (@lem3292881 _86360 q p) (@lem3292885 _86360 q p)). Qed.
Lemma lem3292887 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : ((term460 _86360 q p) = (term461 _86360 q p)) = ((term311 _86360 q p) = (term479 _86360 q p)).
Proof. exact (MK_COMB (@lem3292875 _86360 q p) (@lem3292886 _86360 q p)). Qed.
Lemma lem3292888 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term311 _86360 q p) = (term479 _86360 q p).
Proof. exact (EQ_MP (@lem3292887 _86360 q p) (@lem3292865 _86360 q p)). Qed.
Lemma lem3292985 {_86360 : Type'} (q : _86360 -> Prop) : (term318 _86360 q) = (term480 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292888 _86360 q p)). Qed.
Lemma lem3292986 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292987 {_86360 : Type'} (q : _86360 -> Prop) : (term319 _86360 q) = (term481 _86360 q).
Proof. exact (MK_COMB (@lem3292986 _86360) (@lem3292985 _86360 q)). Qed.
Lemma lem3292989 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3292990 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3292989 (_86360 -> Prop) P Q). Qed.
Lemma lem3292991 {_86360 : Type'} (q : _86360 -> Prop) : (term484 _86360 q) = (term485 _86360 q).
Proof. exact (@lem3292990 _86360 (term486 _86360 q) (term487 _86360 q)). Qed.
Lemma lem3292992 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term488 _86360 q p) = (term473 _86360 q p).
Proof. exact (eq_refl (term488 _86360 q p)). Qed.
Lemma lem3292993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3292994 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term489 _86360 q p) = (term475 _86360 q p).
Proof. exact (MK_COMB (@lem3292993) (@lem3292992 _86360 q p)). Qed.
Lemma lem3292995 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term490 _86360 q p) = (term478 _86360 q p).
Proof. exact (eq_refl (term490 _86360 q p)). Qed.
Lemma lem3292996 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term491 _86360 q p) = (term479 _86360 q p).
Proof. exact (MK_COMB (@lem3292994 _86360 q p) (@lem3292995 _86360 q p)). Qed.
Lemma lem3292997 {_86360 : Type'} (q : _86360 -> Prop) : (term492 _86360 q) = (term480 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3292996 _86360 q p)). Qed.
Lemma lem3292998 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3292999 {_86360 : Type'} (q : _86360 -> Prop) : (term484 _86360 q) = (term481 _86360 q).
Proof. exact (MK_COMB (@lem3292998 _86360) (@lem3292997 _86360 q)). Qed.
Lemma lem3293000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293001 {_86360 : Type'} (q : _86360 -> Prop) : (term493 _86360 q) = (term494 _86360 q).
Proof. exact (MK_COMB (@lem3293000) (@lem3292999 _86360 q)). Qed.
Lemma lem3293002 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term488 _86360 q p) = (term473 _86360 q p).
Proof. exact (eq_refl (term488 _86360 q p)). Qed.
Lemma lem3293003 {_86360 : Type'} (q : _86360 -> Prop) : (term495 _86360 q) = (term486 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3293002 _86360 q p)). Qed.
Lemma lem3293004 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293005 {_86360 : Type'} (q : _86360 -> Prop) : (term496 _86360 q) = (term497 _86360 q).
Proof. exact (MK_COMB (@lem3293004 _86360) (@lem3293003 _86360 q)). Qed.
Lemma lem3293006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293007 {_86360 : Type'} (q : _86360 -> Prop) : (term498 _86360 q) = (term499 _86360 q).
Proof. exact (MK_COMB (@lem3293006) (@lem3293005 _86360 q)). Qed.
Lemma lem3293008 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term490 _86360 q p) = (term478 _86360 q p).
Proof. exact (eq_refl (term490 _86360 q p)). Qed.
Lemma lem3293009 {_86360 : Type'} (q : _86360 -> Prop) : (term500 _86360 q) = (term487 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3293008 _86360 q p)). Qed.
Lemma lem3293010 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293011 {_86360 : Type'} (q : _86360 -> Prop) : (term501 _86360 q) = (term502 _86360 q).
Proof. exact (MK_COMB (@lem3293010 _86360) (@lem3293009 _86360 q)). Qed.
Lemma lem3293012 {_86360 : Type'} (q : _86360 -> Prop) : (term485 _86360 q) = (term503 _86360 q).
Proof. exact (MK_COMB (@lem3293007 _86360 q) (@lem3293011 _86360 q)). Qed.
Lemma lem3293013 {_86360 : Type'} (q : _86360 -> Prop) : ((term484 _86360 q) = (term485 _86360 q)) = ((term481 _86360 q) = (term503 _86360 q)).
Proof. exact (MK_COMB (@lem3293001 _86360 q) (@lem3293012 _86360 q)). Qed.
Lemma lem3293014 {_86360 : Type'} (q : _86360 -> Prop) : (term481 _86360 q) = (term503 _86360 q).
Proof. exact (EQ_MP (@lem3293013 _86360 q) (@lem3292991 _86360 q)). Qed.
Lemma lem3293119 {_86360 : Type'} (q : _86360 -> Prop) : (term319 _86360 q) = (term503 _86360 q).
Proof. exact (TRANS (@lem3292987 _86360 q) (@lem3293014 _86360 q)). Qed.
Lemma lem3293120 {_86360 : Type'} : (term324 _86360) = (term504 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293119 _86360 q)). Qed.
Lemma lem3293121 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293122 {_86360 : Type'} : (term325 _86360) = (term505 _86360).
Proof. exact (MK_COMB (@lem3293121 _86360) (@lem3293120 _86360)). Qed.
Lemma lem3293124 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293125 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3293124 (_86360 -> Prop) P Q). Qed.
Lemma lem3293126 {_86360 : Type'} : (term506 _86360) = (term507 _86360).
Proof. exact (@lem3293125 _86360 (term508 _86360) (term509 _86360)). Qed.
Lemma lem3293127 {_86360 : Type'} (q : _86360 -> Prop) : (term510 _86360 q) = (term497 _86360 q).
Proof. exact (eq_refl (term510 _86360 q)). Qed.
Lemma lem3293128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293129 {_86360 : Type'} (q : _86360 -> Prop) : (term511 _86360 q) = (term499 _86360 q).
Proof. exact (MK_COMB (@lem3293128) (@lem3293127 _86360 q)). Qed.
Lemma lem3293130 {_86360 : Type'} (q : _86360 -> Prop) : (term512 _86360 q) = (term502 _86360 q).
Proof. exact (eq_refl (term512 _86360 q)). Qed.
Lemma lem3293131 {_86360 : Type'} (q : _86360 -> Prop) : (term513 _86360 q) = (term503 _86360 q).
Proof. exact (MK_COMB (@lem3293129 _86360 q) (@lem3293130 _86360 q)). Qed.
Lemma lem3293132 {_86360 : Type'} : (term514 _86360) = (term504 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293131 _86360 q)). Qed.
Lemma lem3293133 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293134 {_86360 : Type'} : (term506 _86360) = (term505 _86360).
Proof. exact (MK_COMB (@lem3293133 _86360) (@lem3293132 _86360)). Qed.
Lemma lem3293135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293136 {_86360 : Type'} : (term515 _86360) = (term516 _86360).
Proof. exact (MK_COMB (@lem3293135) (@lem3293134 _86360)). Qed.
Lemma lem3293137 {_86360 : Type'} (q : _86360 -> Prop) : (term510 _86360 q) = (term497 _86360 q).
Proof. exact (eq_refl (term510 _86360 q)). Qed.
Lemma lem3293138 {_86360 : Type'} : (term517 _86360) = (term508 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293137 _86360 q)). Qed.
Lemma lem3293139 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293140 {_86360 : Type'} : (term518 _86360) = (term519 _86360).
Proof. exact (MK_COMB (@lem3293139 _86360) (@lem3293138 _86360)). Qed.
Lemma lem3293141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293142 {_86360 : Type'} : (term520 _86360) = (term521 _86360).
Proof. exact (MK_COMB (@lem3293141) (@lem3293140 _86360)). Qed.
Lemma lem3293143 {_86360 : Type'} (q : _86360 -> Prop) : (term512 _86360 q) = (term502 _86360 q).
Proof. exact (eq_refl (term512 _86360 q)). Qed.
Lemma lem3293144 {_86360 : Type'} : (term522 _86360) = (term509 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293143 _86360 q)). Qed.
Lemma lem3293145 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293146 {_86360 : Type'} : (term523 _86360) = (term524 _86360).
Proof. exact (MK_COMB (@lem3293145 _86360) (@lem3293144 _86360)). Qed.
Lemma lem3293147 {_86360 : Type'} : (term507 _86360) = (term525 _86360).
Proof. exact (MK_COMB (@lem3293142 _86360) (@lem3293146 _86360)). Qed.
Lemma lem3293148 {_86360 : Type'} : ((term506 _86360) = (term507 _86360)) = ((term505 _86360) = (term525 _86360)).
Proof. exact (MK_COMB (@lem3293136 _86360) (@lem3293147 _86360)). Qed.
Lemma lem3293149 {_86360 : Type'} : (term505 _86360) = (term525 _86360).
Proof. exact (EQ_MP (@lem3293148 _86360) (@lem3293126 _86360)). Qed.
Lemma lem3293262 {_86360 : Type'} : (term325 _86360) = (term525 _86360).
Proof. exact (TRANS (@lem3293122 _86360) (@lem3293149 _86360)). Qed.
Lemma lem3293263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293264 {_86360 : Type'} : (term455 _86360) = (term526 _86360).
Proof. exact (MK_COMB (@lem3293263) (@lem3293262 _86360)). Qed.
Lemma lem3293278 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293279 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term458 _86360 P Q) = (term459 _86360 P Q).
Proof. exact (@lem3293278 _86360 P Q). Qed.
Lemma lem3293280 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term527 _86360 p q r) = (term528 _86360 p q r).
Proof. exact (@lem3293279 _86360 (term529 _86360 p q r) (term530 _86360 p q r)). Qed.
Lemma lem3293281 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term531 _86360 p q r x) = (term342 _86360 p q r x).
Proof. exact (eq_refl (term531 _86360 p q r x)). Qed.
Lemma lem3293282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293283 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term532 _86360 p q r x) = (term344 _86360 p q r x).
Proof. exact (MK_COMB (@lem3293282) (@lem3293281 _86360 p q r x)). Qed.
Lemma lem3293284 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term533 _86360 p q r x) = (term339 _86360 p q r x).
Proof. exact (eq_refl (term533 _86360 p q r x)). Qed.
Lemma lem3293285 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term534 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (MK_COMB (@lem3293283 _86360 p q r x) (@lem3293284 _86360 p q r x)). Qed.
Lemma lem3293286 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term535 _86360 p q r) = (term353 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3293285 _86360 p q r x)). Qed.
Lemma lem3293287 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3293288 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term527 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (MK_COMB (@lem3293287 _86360) (@lem3293286 _86360 p q r)). Qed.
Lemma lem3293289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293290 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term536 _86360 p q r) = (term537 _86360 p q r).
Proof. exact (MK_COMB (@lem3293289) (@lem3293288 _86360 p q r)). Qed.
Lemma lem3293291 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term531 _86360 p q r x) = (term342 _86360 p q r x).
Proof. exact (eq_refl (term531 _86360 p q r x)). Qed.
Lemma lem3293292 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term538 _86360 p q r) = (term529 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3293291 _86360 p q r x)). Qed.
Lemma lem3293293 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3293294 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term539 _86360 p q r) = (term540 _86360 p q r).
Proof. exact (MK_COMB (@lem3293293 _86360) (@lem3293292 _86360 p q r)). Qed.
Lemma lem3293295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293296 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term541 _86360 p q r) = (term542 _86360 p q r).
Proof. exact (MK_COMB (@lem3293295) (@lem3293294 _86360 p q r)). Qed.
Lemma lem3293297 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term533 _86360 p q r x) = (term339 _86360 p q r x).
Proof. exact (eq_refl (term533 _86360 p q r x)). Qed.
Lemma lem3293298 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term543 _86360 p q r) = (term530 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3293297 _86360 p q r x)). Qed.
Lemma lem3293299 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3293300 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term544 _86360 p q r) = (term545 _86360 p q r).
Proof. exact (MK_COMB (@lem3293299 _86360) (@lem3293298 _86360 p q r)). Qed.
Lemma lem3293301 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term528 _86360 p q r) = (term546 _86360 p q r).
Proof. exact (MK_COMB (@lem3293296 _86360 p q r) (@lem3293300 _86360 p q r)). Qed.
Lemma lem3293302 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : ((term527 _86360 p q r) = (term528 _86360 p q r)) = ((term354 _86360 p q r) = (term546 _86360 p q r)).
Proof. exact (MK_COMB (@lem3293290 _86360 p q r) (@lem3293301 _86360 p q r)). Qed.
Lemma lem3293303 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term354 _86360 p q r) = (term546 _86360 p q r).
Proof. exact (EQ_MP (@lem3293302 _86360 p q r) (@lem3293280 _86360 p q r)). Qed.
Lemma lem3293400 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term359 _86360 p q) = (term547 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293303 _86360 p q r)). Qed.
Lemma lem3293401 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293402 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term360 _86360 p q) = (term548 _86360 p q).
Proof. exact (MK_COMB (@lem3293401 _86360) (@lem3293400 _86360 p q)). Qed.
Lemma lem3293404 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293405 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3293404 (_86360 -> Prop) P Q). Qed.
Lemma lem3293406 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term549 _86360 p q) = (term550 _86360 p q).
Proof. exact (@lem3293405 _86360 (term551 _86360 p q) (term552 _86360 p q)). Qed.
Lemma lem3293407 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term553 _86360 p q r) = (term540 _86360 p q r).
Proof. exact (eq_refl (term553 _86360 p q r)). Qed.
Lemma lem3293408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293409 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term554 _86360 p q r) = (term542 _86360 p q r).
Proof. exact (MK_COMB (@lem3293408) (@lem3293407 _86360 p q r)). Qed.
Lemma lem3293410 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term555 _86360 p q r) = (term545 _86360 p q r).
Proof. exact (eq_refl (term555 _86360 p q r)). Qed.
Lemma lem3293411 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term556 _86360 p q r) = (term546 _86360 p q r).
Proof. exact (MK_COMB (@lem3293409 _86360 p q r) (@lem3293410 _86360 p q r)). Qed.
Lemma lem3293412 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term557 _86360 p q) = (term547 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293411 _86360 p q r)). Qed.
Lemma lem3293413 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293414 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term549 _86360 p q) = (term548 _86360 p q).
Proof. exact (MK_COMB (@lem3293413 _86360) (@lem3293412 _86360 p q)). Qed.
Lemma lem3293415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293416 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term558 _86360 p q) = (term559 _86360 p q).
Proof. exact (MK_COMB (@lem3293415) (@lem3293414 _86360 p q)). Qed.
Lemma lem3293417 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term553 _86360 p q r) = (term540 _86360 p q r).
Proof. exact (eq_refl (term553 _86360 p q r)). Qed.
Lemma lem3293418 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term560 _86360 p q) = (term551 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293417 _86360 p q r)). Qed.
Lemma lem3293419 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293420 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term561 _86360 p q) = (term562 _86360 p q).
Proof. exact (MK_COMB (@lem3293419 _86360) (@lem3293418 _86360 p q)). Qed.
Lemma lem3293421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293422 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term563 _86360 p q) = (term564 _86360 p q).
Proof. exact (MK_COMB (@lem3293421) (@lem3293420 _86360 p q)). Qed.
Lemma lem3293423 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term555 _86360 p q r) = (term545 _86360 p q r).
Proof. exact (eq_refl (term555 _86360 p q r)). Qed.
Lemma lem3293424 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term565 _86360 p q) = (term552 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293423 _86360 p q r)). Qed.
Lemma lem3293425 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293426 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term566 _86360 p q) = (term567 _86360 p q).
Proof. exact (MK_COMB (@lem3293425 _86360) (@lem3293424 _86360 p q)). Qed.
Lemma lem3293427 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term550 _86360 p q) = (term568 _86360 p q).
Proof. exact (MK_COMB (@lem3293422 _86360 p q) (@lem3293426 _86360 p q)). Qed.
Lemma lem3293428 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term549 _86360 p q) = (term550 _86360 p q)) = ((term548 _86360 p q) = (term568 _86360 p q)).
Proof. exact (MK_COMB (@lem3293416 _86360 p q) (@lem3293427 _86360 p q)). Qed.
Lemma lem3293429 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term548 _86360 p q) = (term568 _86360 p q).
Proof. exact (EQ_MP (@lem3293428 _86360 p q) (@lem3293406 _86360 p q)). Qed.
Lemma lem3293534 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term360 _86360 p q) = (term568 _86360 p q).
Proof. exact (TRANS (@lem3293402 _86360 p q) (@lem3293429 _86360 p q)). Qed.
Lemma lem3293535 {_86360 : Type'} (q : _86360 -> Prop) : (term365 _86360 q) = (term569 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3293534 _86360 p q)). Qed.
Lemma lem3293536 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293537 {_86360 : Type'} (q : _86360 -> Prop) : (term366 _86360 q) = (term570 _86360 q).
Proof. exact (MK_COMB (@lem3293536 _86360) (@lem3293535 _86360 q)). Qed.
Lemma lem3293539 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293540 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3293539 (_86360 -> Prop) P Q). Qed.
Lemma lem3293541 {_86360 : Type'} (q : _86360 -> Prop) : (term571 _86360 q) = (term572 _86360 q).
Proof. exact (@lem3293540 _86360 (term573 _86360 q) (term574 _86360 q)). Qed.
Lemma lem3293542 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term575 _86360 q p) = (term562 _86360 p q).
Proof. exact (eq_refl (term575 _86360 q p)). Qed.
Lemma lem3293543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293544 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term576 _86360 q p) = (term564 _86360 p q).
Proof. exact (MK_COMB (@lem3293543) (@lem3293542 _86360 p q)). Qed.
Lemma lem3293545 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term577 _86360 q p) = (term567 _86360 p q).
Proof. exact (eq_refl (term577 _86360 q p)). Qed.
Lemma lem3293546 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term578 _86360 q p) = (term568 _86360 p q).
Proof. exact (MK_COMB (@lem3293544 _86360 p q) (@lem3293545 _86360 p q)). Qed.
Lemma lem3293547 {_86360 : Type'} (q : _86360 -> Prop) : (term579 _86360 q) = (term569 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3293546 _86360 p q)). Qed.
Lemma lem3293548 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293549 {_86360 : Type'} (q : _86360 -> Prop) : (term571 _86360 q) = (term570 _86360 q).
Proof. exact (MK_COMB (@lem3293548 _86360) (@lem3293547 _86360 q)). Qed.
Lemma lem3293550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293551 {_86360 : Type'} (q : _86360 -> Prop) : (term580 _86360 q) = (term581 _86360 q).
Proof. exact (MK_COMB (@lem3293550) (@lem3293549 _86360 q)). Qed.
Lemma lem3293552 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term575 _86360 q p) = (term562 _86360 p q).
Proof. exact (eq_refl (term575 _86360 q p)). Qed.
Lemma lem3293553 {_86360 : Type'} (q : _86360 -> Prop) : (term582 _86360 q) = (term573 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3293552 _86360 p q)). Qed.
Lemma lem3293554 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293555 {_86360 : Type'} (q : _86360 -> Prop) : (term583 _86360 q) = (term584 _86360 q).
Proof. exact (MK_COMB (@lem3293554 _86360) (@lem3293553 _86360 q)). Qed.
Lemma lem3293556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293557 {_86360 : Type'} (q : _86360 -> Prop) : (term585 _86360 q) = (term586 _86360 q).
Proof. exact (MK_COMB (@lem3293556) (@lem3293555 _86360 q)). Qed.
Lemma lem3293558 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term577 _86360 q p) = (term567 _86360 p q).
Proof. exact (eq_refl (term577 _86360 q p)). Qed.
Lemma lem3293559 {_86360 : Type'} (q : _86360 -> Prop) : (term587 _86360 q) = (term574 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3293558 _86360 p q)). Qed.
Lemma lem3293560 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293561 {_86360 : Type'} (q : _86360 -> Prop) : (term588 _86360 q) = (term589 _86360 q).
Proof. exact (MK_COMB (@lem3293560 _86360) (@lem3293559 _86360 q)). Qed.
Lemma lem3293562 {_86360 : Type'} (q : _86360 -> Prop) : (term572 _86360 q) = (term590 _86360 q).
Proof. exact (MK_COMB (@lem3293557 _86360 q) (@lem3293561 _86360 q)). Qed.
Lemma lem3293563 {_86360 : Type'} (q : _86360 -> Prop) : ((term571 _86360 q) = (term572 _86360 q)) = ((term570 _86360 q) = (term590 _86360 q)).
Proof. exact (MK_COMB (@lem3293551 _86360 q) (@lem3293562 _86360 q)). Qed.
Lemma lem3293564 {_86360 : Type'} (q : _86360 -> Prop) : (term570 _86360 q) = (term590 _86360 q).
Proof. exact (EQ_MP (@lem3293563 _86360 q) (@lem3293541 _86360 q)). Qed.
Lemma lem3293677 {_86360 : Type'} (q : _86360 -> Prop) : (term366 _86360 q) = (term590 _86360 q).
Proof. exact (TRANS (@lem3293537 _86360 q) (@lem3293564 _86360 q)). Qed.
Lemma lem3293678 {_86360 : Type'} : (term371 _86360) = (term591 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293677 _86360 q)). Qed.
Lemma lem3293679 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293680 {_86360 : Type'} : (term372 _86360) = (term592 _86360).
Proof. exact (MK_COMB (@lem3293679 _86360) (@lem3293678 _86360)). Qed.
Lemma lem3293682 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293683 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3293682 (_86360 -> Prop) P Q). Qed.
Lemma lem3293684 {_86360 : Type'} : (term593 _86360) = (term594 _86360).
Proof. exact (@lem3293683 _86360 (term595 _86360) (term596 _86360)). Qed.
Lemma lem3293685 {_86360 : Type'} (q : _86360 -> Prop) : (term597 _86360 q) = (term584 _86360 q).
Proof. exact (eq_refl (term597 _86360 q)). Qed.
Lemma lem3293686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293687 {_86360 : Type'} (q : _86360 -> Prop) : (term598 _86360 q) = (term586 _86360 q).
Proof. exact (MK_COMB (@lem3293686) (@lem3293685 _86360 q)). Qed.
Lemma lem3293688 {_86360 : Type'} (q : _86360 -> Prop) : (term599 _86360 q) = (term589 _86360 q).
Proof. exact (eq_refl (term599 _86360 q)). Qed.
Lemma lem3293689 {_86360 : Type'} (q : _86360 -> Prop) : (term600 _86360 q) = (term590 _86360 q).
Proof. exact (MK_COMB (@lem3293687 _86360 q) (@lem3293688 _86360 q)). Qed.
Lemma lem3293690 {_86360 : Type'} : (term601 _86360) = (term591 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293689 _86360 q)). Qed.
Lemma lem3293691 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293692 {_86360 : Type'} : (term593 _86360) = (term592 _86360).
Proof. exact (MK_COMB (@lem3293691 _86360) (@lem3293690 _86360)). Qed.
Lemma lem3293693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293694 {_86360 : Type'} : (term602 _86360) = (term603 _86360).
Proof. exact (MK_COMB (@lem3293693) (@lem3293692 _86360)). Qed.
Lemma lem3293695 {_86360 : Type'} (q : _86360 -> Prop) : (term597 _86360 q) = (term584 _86360 q).
Proof. exact (eq_refl (term597 _86360 q)). Qed.
Lemma lem3293696 {_86360 : Type'} : (term604 _86360) = (term595 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293695 _86360 q)). Qed.
Lemma lem3293697 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293698 {_86360 : Type'} : (term605 _86360) = (term606 _86360).
Proof. exact (MK_COMB (@lem3293697 _86360) (@lem3293696 _86360)). Qed.
Lemma lem3293699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293700 {_86360 : Type'} : (term607 _86360) = (term608 _86360).
Proof. exact (MK_COMB (@lem3293699) (@lem3293698 _86360)). Qed.
Lemma lem3293701 {_86360 : Type'} (q : _86360 -> Prop) : (term599 _86360 q) = (term589 _86360 q).
Proof. exact (eq_refl (term599 _86360 q)). Qed.
Lemma lem3293702 {_86360 : Type'} : (term609 _86360) = (term596 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3293701 _86360 q)). Qed.
Lemma lem3293703 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293704 {_86360 : Type'} : (term610 _86360) = (term611 _86360).
Proof. exact (MK_COMB (@lem3293703 _86360) (@lem3293702 _86360)). Qed.
Lemma lem3293705 {_86360 : Type'} : (term594 _86360) = (term612 _86360).
Proof. exact (MK_COMB (@lem3293700 _86360) (@lem3293704 _86360)). Qed.
Lemma lem3293706 {_86360 : Type'} : ((term593 _86360) = (term594 _86360)) = ((term592 _86360) = (term612 _86360)).
Proof. exact (MK_COMB (@lem3293694 _86360) (@lem3293705 _86360)). Qed.
Lemma lem3293707 {_86360 : Type'} : (term592 _86360) = (term612 _86360).
Proof. exact (EQ_MP (@lem3293706 _86360) (@lem3293684 _86360)). Qed.
Lemma lem3293828 {_86360 : Type'} : (term372 _86360) = (term612 _86360).
Proof. exact (TRANS (@lem3293680 _86360) (@lem3293707 _86360)). Qed.
Lemma lem3293829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293830 {_86360 : Type'} : (term450 _86360) = (term613 _86360).
Proof. exact (MK_COMB (@lem3293829) (@lem3293828 _86360)). Qed.
Lemma lem3293844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293845 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term458 _86360 P Q) = (term459 _86360 P Q).
Proof. exact (@lem3293844 _86360 P Q). Qed.
Lemma lem3293846 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term614 _86360 q p r) = (term615 _86360 q p r).
Proof. exact (@lem3293845 _86360 (term616 _86360 q p r) (term617 _86360 q p r)). Qed.
Lemma lem3293847 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term618 _86360 q p r x) = (term379 _86360 q p r x).
Proof. exact (eq_refl (term618 _86360 q p r x)). Qed.
Lemma lem3293848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293849 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term619 _86360 q p r x) = (term381 _86360 q p r x).
Proof. exact (MK_COMB (@lem3293848) (@lem3293847 _86360 q p r x)). Qed.
Lemma lem3293850 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term620 _86360 q p r x) = (term376 _86360 q p r x).
Proof. exact (eq_refl (term620 _86360 q p r x)). Qed.
Lemma lem3293851 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term621 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (MK_COMB (@lem3293849 _86360 q p r x) (@lem3293850 _86360 q p r x)). Qed.
Lemma lem3293852 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term622 _86360 q p r) = (term390 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3293851 _86360 q p r x)). Qed.
Lemma lem3293853 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3293854 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term614 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (MK_COMB (@lem3293853 _86360) (@lem3293852 _86360 q p r)). Qed.
Lemma lem3293855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293856 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term623 _86360 q p r) = (term624 _86360 q p r).
Proof. exact (MK_COMB (@lem3293855) (@lem3293854 _86360 q p r)). Qed.
Lemma lem3293857 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term618 _86360 q p r x) = (term379 _86360 q p r x).
Proof. exact (eq_refl (term618 _86360 q p r x)). Qed.
Lemma lem3293858 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term625 _86360 q p r) = (term616 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3293857 _86360 q p r x)). Qed.
Lemma lem3293859 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3293860 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term626 _86360 q p r) = (term627 _86360 q p r).
Proof. exact (MK_COMB (@lem3293859 _86360) (@lem3293858 _86360 q p r)). Qed.
Lemma lem3293861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293862 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term628 _86360 q p r) = (term629 _86360 q p r).
Proof. exact (MK_COMB (@lem3293861) (@lem3293860 _86360 q p r)). Qed.
Lemma lem3293863 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term620 _86360 q p r x) = (term376 _86360 q p r x).
Proof. exact (eq_refl (term620 _86360 q p r x)). Qed.
Lemma lem3293864 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term630 _86360 q p r) = (term617 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3293863 _86360 q p r x)). Qed.
Lemma lem3293865 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3293866 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term631 _86360 q p r) = (term632 _86360 q p r).
Proof. exact (MK_COMB (@lem3293865 _86360) (@lem3293864 _86360 q p r)). Qed.
Lemma lem3293867 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term615 _86360 q p r) = (term633 _86360 q p r).
Proof. exact (MK_COMB (@lem3293862 _86360 q p r) (@lem3293866 _86360 q p r)). Qed.
Lemma lem3293868 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : ((term614 _86360 q p r) = (term615 _86360 q p r)) = ((term391 _86360 q p r) = (term633 _86360 q p r)).
Proof. exact (MK_COMB (@lem3293856 _86360 q p r) (@lem3293867 _86360 q p r)). Qed.
Lemma lem3293869 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term391 _86360 q p r) = (term633 _86360 q p r).
Proof. exact (EQ_MP (@lem3293868 _86360 q p r) (@lem3293846 _86360 q p r)). Qed.
Lemma lem3293966 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term396 _86360 q p) = (term634 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293869 _86360 q p r)). Qed.
Lemma lem3293967 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293968 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term397 _86360 q p) = (term635 _86360 q p).
Proof. exact (MK_COMB (@lem3293967 _86360) (@lem3293966 _86360 q p)). Qed.
Lemma lem3293970 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3293971 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3293970 (_86360 -> Prop) P Q). Qed.
Lemma lem3293972 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term636 _86360 q p) = (term637 _86360 q p).
Proof. exact (@lem3293971 _86360 (term638 _86360 q p) (term639 _86360 q p)). Qed.
Lemma lem3293973 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term640 _86360 q p r) = (term627 _86360 q p r).
Proof. exact (eq_refl (term640 _86360 q p r)). Qed.
Lemma lem3293974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293975 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term641 _86360 q p r) = (term629 _86360 q p r).
Proof. exact (MK_COMB (@lem3293974) (@lem3293973 _86360 q p r)). Qed.
Lemma lem3293976 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term642 _86360 q p r) = (term632 _86360 q p r).
Proof. exact (eq_refl (term642 _86360 q p r)). Qed.
Lemma lem3293977 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term643 _86360 q p r) = (term633 _86360 q p r).
Proof. exact (MK_COMB (@lem3293975 _86360 q p r) (@lem3293976 _86360 q p r)). Qed.
Lemma lem3293978 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term644 _86360 q p) = (term634 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293977 _86360 q p r)). Qed.
Lemma lem3293979 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293980 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term636 _86360 q p) = (term635 _86360 q p).
Proof. exact (MK_COMB (@lem3293979 _86360) (@lem3293978 _86360 q p)). Qed.
Lemma lem3293981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3293982 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term645 _86360 q p) = (term646 _86360 q p).
Proof. exact (MK_COMB (@lem3293981) (@lem3293980 _86360 q p)). Qed.
Lemma lem3293983 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term640 _86360 q p r) = (term627 _86360 q p r).
Proof. exact (eq_refl (term640 _86360 q p r)). Qed.
Lemma lem3293984 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term647 _86360 q p) = (term638 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293983 _86360 q p r)). Qed.
Lemma lem3293985 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293986 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term648 _86360 q p) = (term649 _86360 q p).
Proof. exact (MK_COMB (@lem3293985 _86360) (@lem3293984 _86360 q p)). Qed.
Lemma lem3293987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3293988 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term650 _86360 q p) = (term651 _86360 q p).
Proof. exact (MK_COMB (@lem3293987) (@lem3293986 _86360 q p)). Qed.
Lemma lem3293989 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term642 _86360 q p r) = (term632 _86360 q p r).
Proof. exact (eq_refl (term642 _86360 q p r)). Qed.
Lemma lem3293990 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term652 _86360 q p) = (term639 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3293989 _86360 q p r)). Qed.
Lemma lem3293991 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3293992 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term653 _86360 q p) = (term654 _86360 q p).
Proof. exact (MK_COMB (@lem3293991 _86360) (@lem3293990 _86360 q p)). Qed.
Lemma lem3293993 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term637 _86360 q p) = (term655 _86360 q p).
Proof. exact (MK_COMB (@lem3293988 _86360 q p) (@lem3293992 _86360 q p)). Qed.
Lemma lem3293994 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : ((term636 _86360 q p) = (term637 _86360 q p)) = ((term635 _86360 q p) = (term655 _86360 q p)).
Proof. exact (MK_COMB (@lem3293982 _86360 q p) (@lem3293993 _86360 q p)). Qed.
Lemma lem3293995 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term635 _86360 q p) = (term655 _86360 q p).
Proof. exact (EQ_MP (@lem3293994 _86360 q p) (@lem3293972 _86360 q p)). Qed.
Lemma lem3294100 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term397 _86360 q p) = (term655 _86360 q p).
Proof. exact (TRANS (@lem3293968 _86360 q p) (@lem3293995 _86360 q p)). Qed.
Lemma lem3294101 {_86360 : Type'} (q : _86360 -> Prop) : (term402 _86360 q) = (term656 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294100 _86360 q p)). Qed.
Lemma lem3294102 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294103 {_86360 : Type'} (q : _86360 -> Prop) : (term403 _86360 q) = (term657 _86360 q).
Proof. exact (MK_COMB (@lem3294102 _86360) (@lem3294101 _86360 q)). Qed.
Lemma lem3294105 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3294106 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3294105 (_86360 -> Prop) P Q). Qed.
Lemma lem3294107 {_86360 : Type'} (q : _86360 -> Prop) : (term658 _86360 q) = (term659 _86360 q).
Proof. exact (@lem3294106 _86360 (term660 _86360 q) (term661 _86360 q)). Qed.
Lemma lem3294108 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term662 _86360 q p) = (term649 _86360 q p).
Proof. exact (eq_refl (term662 _86360 q p)). Qed.
Lemma lem3294109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294110 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term663 _86360 q p) = (term651 _86360 q p).
Proof. exact (MK_COMB (@lem3294109) (@lem3294108 _86360 q p)). Qed.
Lemma lem3294111 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term664 _86360 q p) = (term654 _86360 q p).
Proof. exact (eq_refl (term664 _86360 q p)). Qed.
Lemma lem3294112 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term665 _86360 q p) = (term655 _86360 q p).
Proof. exact (MK_COMB (@lem3294110 _86360 q p) (@lem3294111 _86360 q p)). Qed.
Lemma lem3294113 {_86360 : Type'} (q : _86360 -> Prop) : (term666 _86360 q) = (term656 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294112 _86360 q p)). Qed.
Lemma lem3294114 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294115 {_86360 : Type'} (q : _86360 -> Prop) : (term658 _86360 q) = (term657 _86360 q).
Proof. exact (MK_COMB (@lem3294114 _86360) (@lem3294113 _86360 q)). Qed.
Lemma lem3294116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294117 {_86360 : Type'} (q : _86360 -> Prop) : (term667 _86360 q) = (term668 _86360 q).
Proof. exact (MK_COMB (@lem3294116) (@lem3294115 _86360 q)). Qed.
Lemma lem3294118 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term662 _86360 q p) = (term649 _86360 q p).
Proof. exact (eq_refl (term662 _86360 q p)). Qed.
Lemma lem3294119 {_86360 : Type'} (q : _86360 -> Prop) : (term669 _86360 q) = (term660 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294118 _86360 q p)). Qed.
Lemma lem3294120 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294121 {_86360 : Type'} (q : _86360 -> Prop) : (term670 _86360 q) = (term671 _86360 q).
Proof. exact (MK_COMB (@lem3294120 _86360) (@lem3294119 _86360 q)). Qed.
Lemma lem3294122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294123 {_86360 : Type'} (q : _86360 -> Prop) : (term672 _86360 q) = (term673 _86360 q).
Proof. exact (MK_COMB (@lem3294122) (@lem3294121 _86360 q)). Qed.
Lemma lem3294124 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term664 _86360 q p) = (term654 _86360 q p).
Proof. exact (eq_refl (term664 _86360 q p)). Qed.
Lemma lem3294125 {_86360 : Type'} (q : _86360 -> Prop) : (term674 _86360 q) = (term661 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294124 _86360 q p)). Qed.
Lemma lem3294126 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294127 {_86360 : Type'} (q : _86360 -> Prop) : (term675 _86360 q) = (term676 _86360 q).
Proof. exact (MK_COMB (@lem3294126 _86360) (@lem3294125 _86360 q)). Qed.
Lemma lem3294128 {_86360 : Type'} (q : _86360 -> Prop) : (term659 _86360 q) = (term677 _86360 q).
Proof. exact (MK_COMB (@lem3294123 _86360 q) (@lem3294127 _86360 q)). Qed.
Lemma lem3294129 {_86360 : Type'} (q : _86360 -> Prop) : ((term658 _86360 q) = (term659 _86360 q)) = ((term657 _86360 q) = (term677 _86360 q)).
Proof. exact (MK_COMB (@lem3294117 _86360 q) (@lem3294128 _86360 q)). Qed.
Lemma lem3294130 {_86360 : Type'} (q : _86360 -> Prop) : (term657 _86360 q) = (term677 _86360 q).
Proof. exact (EQ_MP (@lem3294129 _86360 q) (@lem3294107 _86360 q)). Qed.
Lemma lem3294243 {_86360 : Type'} (q : _86360 -> Prop) : (term403 _86360 q) = (term677 _86360 q).
Proof. exact (TRANS (@lem3294103 _86360 q) (@lem3294130 _86360 q)). Qed.
Lemma lem3294244 {_86360 : Type'} : (term408 _86360) = (term678 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294243 _86360 q)). Qed.
Lemma lem3294245 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294246 {_86360 : Type'} : (term409 _86360) = (term679 _86360).
Proof. exact (MK_COMB (@lem3294245 _86360) (@lem3294244 _86360)). Qed.
Lemma lem3294248 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3294249 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3294248 (_86360 -> Prop) P Q). Qed.
Lemma lem3294250 {_86360 : Type'} : (term680 _86360) = (term681 _86360).
Proof. exact (@lem3294249 _86360 (term682 _86360) (term683 _86360)). Qed.
Lemma lem3294251 {_86360 : Type'} (q : _86360 -> Prop) : (term684 _86360 q) = (term671 _86360 q).
Proof. exact (eq_refl (term684 _86360 q)). Qed.
Lemma lem3294252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294253 {_86360 : Type'} (q : _86360 -> Prop) : (term685 _86360 q) = (term673 _86360 q).
Proof. exact (MK_COMB (@lem3294252) (@lem3294251 _86360 q)). Qed.
Lemma lem3294254 {_86360 : Type'} (q : _86360 -> Prop) : (term686 _86360 q) = (term676 _86360 q).
Proof. exact (eq_refl (term686 _86360 q)). Qed.
Lemma lem3294255 {_86360 : Type'} (q : _86360 -> Prop) : (term687 _86360 q) = (term677 _86360 q).
Proof. exact (MK_COMB (@lem3294253 _86360 q) (@lem3294254 _86360 q)). Qed.
Lemma lem3294256 {_86360 : Type'} : (term688 _86360) = (term678 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294255 _86360 q)). Qed.
Lemma lem3294257 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294258 {_86360 : Type'} : (term680 _86360) = (term679 _86360).
Proof. exact (MK_COMB (@lem3294257 _86360) (@lem3294256 _86360)). Qed.
Lemma lem3294259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294260 {_86360 : Type'} : (term689 _86360) = (term690 _86360).
Proof. exact (MK_COMB (@lem3294259) (@lem3294258 _86360)). Qed.
Lemma lem3294261 {_86360 : Type'} (q : _86360 -> Prop) : (term684 _86360 q) = (term671 _86360 q).
Proof. exact (eq_refl (term684 _86360 q)). Qed.
Lemma lem3294262 {_86360 : Type'} : (term691 _86360) = (term682 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294261 _86360 q)). Qed.
Lemma lem3294263 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294264 {_86360 : Type'} : (term692 _86360) = (term693 _86360).
Proof. exact (MK_COMB (@lem3294263 _86360) (@lem3294262 _86360)). Qed.
Lemma lem3294265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294266 {_86360 : Type'} : (term694 _86360) = (term695 _86360).
Proof. exact (MK_COMB (@lem3294265) (@lem3294264 _86360)). Qed.
Lemma lem3294267 {_86360 : Type'} (q : _86360 -> Prop) : (term686 _86360 q) = (term676 _86360 q).
Proof. exact (eq_refl (term686 _86360 q)). Qed.
Lemma lem3294268 {_86360 : Type'} : (term696 _86360) = (term683 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294267 _86360 q)). Qed.
Lemma lem3294269 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294270 {_86360 : Type'} : (term697 _86360) = (term698 _86360).
Proof. exact (MK_COMB (@lem3294269 _86360) (@lem3294268 _86360)). Qed.
Lemma lem3294271 {_86360 : Type'} : (term681 _86360) = (term699 _86360).
Proof. exact (MK_COMB (@lem3294266 _86360) (@lem3294270 _86360)). Qed.
Lemma lem3294272 {_86360 : Type'} : ((term680 _86360) = (term681 _86360)) = ((term679 _86360) = (term699 _86360)).
Proof. exact (MK_COMB (@lem3294260 _86360) (@lem3294271 _86360)). Qed.
Lemma lem3294273 {_86360 : Type'} : (term679 _86360) = (term699 _86360).
Proof. exact (EQ_MP (@lem3294272 _86360) (@lem3294250 _86360)). Qed.
Lemma lem3294394 {_86360 : Type'} : (term409 _86360) = (term699 _86360).
Proof. exact (TRANS (@lem3294246 _86360) (@lem3294273 _86360)). Qed.
Lemma lem3294395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294396 {_86360 : Type'} : (term445 _86360) = (term700 _86360).
Proof. exact (MK_COMB (@lem3294395) (@lem3294394 _86360)). Qed.
Lemma lem3294406 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3294407 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term458 _86360 P Q) = (term459 _86360 P Q).
Proof. exact (@lem3294406 _86360 P Q). Qed.
Lemma lem3294408 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term701 _86360 p q) = (term702 _86360 p q).
Proof. exact (@lem3294407 _86360 (term703 _86360 p q) (term704 _86360 p q)). Qed.
Lemma lem3294409 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term705 _86360 p q x) = (term419 _86360 p q x).
Proof. exact (eq_refl (term705 _86360 p q x)). Qed.
Lemma lem3294410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294411 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term706 _86360 p q x) = (term421 _86360 p q x).
Proof. exact (MK_COMB (@lem3294410) (@lem3294409 _86360 p q x)). Qed.
Lemma lem3294412 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term707 _86360 p q x) = (term416 _86360 p q x).
Proof. exact (eq_refl (term707 _86360 p q x)). Qed.
Lemma lem3294413 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term708 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (MK_COMB (@lem3294411 _86360 p q x) (@lem3294412 _86360 p q x)). Qed.
Lemma lem3294414 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term709 _86360 p q) = (term430 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3294413 _86360 p q x)). Qed.
Lemma lem3294415 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294416 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term701 _86360 p q) = (term431 _86360 p q).
Proof. exact (MK_COMB (@lem3294415 _86360) (@lem3294414 _86360 p q)). Qed.
Lemma lem3294417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294418 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term710 _86360 p q) = (term711 _86360 p q).
Proof. exact (MK_COMB (@lem3294417) (@lem3294416 _86360 p q)). Qed.
Lemma lem3294419 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term705 _86360 p q x) = (term419 _86360 p q x).
Proof. exact (eq_refl (term705 _86360 p q x)). Qed.
Lemma lem3294420 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term712 _86360 p q) = (term703 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3294419 _86360 p q x)). Qed.
Lemma lem3294421 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294422 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term713 _86360 p q) = (term714 _86360 p q).
Proof. exact (MK_COMB (@lem3294421 _86360) (@lem3294420 _86360 p q)). Qed.
Lemma lem3294423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294424 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term715 _86360 p q) = (term716 _86360 p q).
Proof. exact (MK_COMB (@lem3294423) (@lem3294422 _86360 p q)). Qed.
Lemma lem3294425 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term707 _86360 p q x) = (term416 _86360 p q x).
Proof. exact (eq_refl (term707 _86360 p q x)). Qed.
Lemma lem3294426 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term717 _86360 p q) = (term704 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3294425 _86360 p q x)). Qed.
Lemma lem3294427 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294428 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term718 _86360 p q) = (term719 _86360 p q).
Proof. exact (MK_COMB (@lem3294427 _86360) (@lem3294426 _86360 p q)). Qed.
Lemma lem3294429 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term702 _86360 p q) = (term720 _86360 p q).
Proof. exact (MK_COMB (@lem3294424 _86360 p q) (@lem3294428 _86360 p q)). Qed.
Lemma lem3294430 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term701 _86360 p q) = (term702 _86360 p q)) = ((term431 _86360 p q) = (term720 _86360 p q)).
Proof. exact (MK_COMB (@lem3294418 _86360 p q) (@lem3294429 _86360 p q)). Qed.
Lemma lem3294431 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term431 _86360 p q) = (term720 _86360 p q).
Proof. exact (EQ_MP (@lem3294430 _86360 p q) (@lem3294408 _86360 p q)). Qed.
Lemma lem3294528 {_86360 : Type'} (q : _86360 -> Prop) : (term436 _86360 q) = (term721 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294431 _86360 p q)). Qed.
Lemma lem3294529 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294530 {_86360 : Type'} (q : _86360 -> Prop) : (term437 _86360 q) = (term722 _86360 q).
Proof. exact (MK_COMB (@lem3294529 _86360) (@lem3294528 _86360 q)). Qed.
Lemma lem3294532 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3294533 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3294532 (_86360 -> Prop) P Q). Qed.
Lemma lem3294534 {_86360 : Type'} (q : _86360 -> Prop) : (term723 _86360 q) = (term724 _86360 q).
Proof. exact (@lem3294533 _86360 (term725 _86360 q) (term726 _86360 q)). Qed.
Lemma lem3294535 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term727 _86360 q p) = (term714 _86360 p q).
Proof. exact (eq_refl (term727 _86360 q p)). Qed.
Lemma lem3294536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294537 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term728 _86360 q p) = (term716 _86360 p q).
Proof. exact (MK_COMB (@lem3294536) (@lem3294535 _86360 p q)). Qed.
Lemma lem3294538 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term729 _86360 q p) = (term719 _86360 p q).
Proof. exact (eq_refl (term729 _86360 q p)). Qed.
Lemma lem3294539 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term730 _86360 q p) = (term720 _86360 p q).
Proof. exact (MK_COMB (@lem3294537 _86360 p q) (@lem3294538 _86360 p q)). Qed.
Lemma lem3294540 {_86360 : Type'} (q : _86360 -> Prop) : (term731 _86360 q) = (term721 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294539 _86360 p q)). Qed.
Lemma lem3294541 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294542 {_86360 : Type'} (q : _86360 -> Prop) : (term723 _86360 q) = (term722 _86360 q).
Proof. exact (MK_COMB (@lem3294541 _86360) (@lem3294540 _86360 q)). Qed.
Lemma lem3294543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294544 {_86360 : Type'} (q : _86360 -> Prop) : (term732 _86360 q) = (term733 _86360 q).
Proof. exact (MK_COMB (@lem3294543) (@lem3294542 _86360 q)). Qed.
Lemma lem3294545 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term727 _86360 q p) = (term714 _86360 p q).
Proof. exact (eq_refl (term727 _86360 q p)). Qed.
Lemma lem3294546 {_86360 : Type'} (q : _86360 -> Prop) : (term734 _86360 q) = (term725 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294545 _86360 p q)). Qed.
Lemma lem3294547 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294548 {_86360 : Type'} (q : _86360 -> Prop) : (term735 _86360 q) = (term736 _86360 q).
Proof. exact (MK_COMB (@lem3294547 _86360) (@lem3294546 _86360 q)). Qed.
Lemma lem3294549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294550 {_86360 : Type'} (q : _86360 -> Prop) : (term737 _86360 q) = (term738 _86360 q).
Proof. exact (MK_COMB (@lem3294549) (@lem3294548 _86360 q)). Qed.
Lemma lem3294551 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term729 _86360 q p) = (term719 _86360 p q).
Proof. exact (eq_refl (term729 _86360 q p)). Qed.
Lemma lem3294552 {_86360 : Type'} (q : _86360 -> Prop) : (term739 _86360 q) = (term726 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294551 _86360 p q)). Qed.
Lemma lem3294553 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294554 {_86360 : Type'} (q : _86360 -> Prop) : (term740 _86360 q) = (term741 _86360 q).
Proof. exact (MK_COMB (@lem3294553 _86360) (@lem3294552 _86360 q)). Qed.
Lemma lem3294555 {_86360 : Type'} (q : _86360 -> Prop) : (term724 _86360 q) = (term742 _86360 q).
Proof. exact (MK_COMB (@lem3294550 _86360 q) (@lem3294554 _86360 q)). Qed.
Lemma lem3294556 {_86360 : Type'} (q : _86360 -> Prop) : ((term723 _86360 q) = (term724 _86360 q)) = ((term722 _86360 q) = (term742 _86360 q)).
Proof. exact (MK_COMB (@lem3294544 _86360 q) (@lem3294555 _86360 q)). Qed.
Lemma lem3294557 {_86360 : Type'} (q : _86360 -> Prop) : (term722 _86360 q) = (term742 _86360 q).
Proof. exact (EQ_MP (@lem3294556 _86360 q) (@lem3294534 _86360 q)). Qed.
Lemma lem3294662 {_86360 : Type'} (q : _86360 -> Prop) : (term437 _86360 q) = (term742 _86360 q).
Proof. exact (TRANS (@lem3294530 _86360 q) (@lem3294557 _86360 q)). Qed.
Lemma lem3294663 {_86360 : Type'} : (term442 _86360) = (term743 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294662 _86360 q)). Qed.
Lemma lem3294664 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294665 {_86360 : Type'} : (term443 _86360) = (term744 _86360).
Proof. exact (MK_COMB (@lem3294664 _86360) (@lem3294663 _86360)). Qed.
Lemma lem3294667 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term458 A P Q) = (term459 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3294668 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term482 _86360 P Q) = (term483 _86360 P Q).
Proof. exact (@lem3294667 (_86360 -> Prop) P Q). Qed.
Lemma lem3294669 {_86360 : Type'} : (term745 _86360) = (term746 _86360).
Proof. exact (@lem3294668 _86360 (term747 _86360) (term748 _86360)). Qed.
Lemma lem3294670 {_86360 : Type'} (q : _86360 -> Prop) : (term749 _86360 q) = (term736 _86360 q).
Proof. exact (eq_refl (term749 _86360 q)). Qed.
Lemma lem3294671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294672 {_86360 : Type'} (q : _86360 -> Prop) : (term750 _86360 q) = (term738 _86360 q).
Proof. exact (MK_COMB (@lem3294671) (@lem3294670 _86360 q)). Qed.
Lemma lem3294673 {_86360 : Type'} (q : _86360 -> Prop) : (term751 _86360 q) = (term741 _86360 q).
Proof. exact (eq_refl (term751 _86360 q)). Qed.
Lemma lem3294674 {_86360 : Type'} (q : _86360 -> Prop) : (term752 _86360 q) = (term742 _86360 q).
Proof. exact (MK_COMB (@lem3294672 _86360 q) (@lem3294673 _86360 q)). Qed.
Lemma lem3294675 {_86360 : Type'} : (term753 _86360) = (term743 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294674 _86360 q)). Qed.
Lemma lem3294676 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294677 {_86360 : Type'} : (term745 _86360) = (term744 _86360).
Proof. exact (MK_COMB (@lem3294676 _86360) (@lem3294675 _86360)). Qed.
Lemma lem3294678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294679 {_86360 : Type'} : (term754 _86360) = (term755 _86360).
Proof. exact (MK_COMB (@lem3294678) (@lem3294677 _86360)). Qed.
Lemma lem3294680 {_86360 : Type'} (q : _86360 -> Prop) : (term749 _86360 q) = (term736 _86360 q).
Proof. exact (eq_refl (term749 _86360 q)). Qed.
Lemma lem3294681 {_86360 : Type'} : (term756 _86360) = (term747 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294680 _86360 q)). Qed.
Lemma lem3294682 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294683 {_86360 : Type'} : (term757 _86360) = (term758 _86360).
Proof. exact (MK_COMB (@lem3294682 _86360) (@lem3294681 _86360)). Qed.
Lemma lem3294684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294685 {_86360 : Type'} : (term759 _86360) = (term760 _86360).
Proof. exact (MK_COMB (@lem3294684) (@lem3294683 _86360)). Qed.
Lemma lem3294686 {_86360 : Type'} (q : _86360 -> Prop) : (term751 _86360 q) = (term741 _86360 q).
Proof. exact (eq_refl (term751 _86360 q)). Qed.
Lemma lem3294687 {_86360 : Type'} : (term761 _86360) = (term748 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294686 _86360 q)). Qed.
Lemma lem3294688 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294689 {_86360 : Type'} : (term762 _86360) = (term763 _86360).
Proof. exact (MK_COMB (@lem3294688 _86360) (@lem3294687 _86360)). Qed.
Lemma lem3294690 {_86360 : Type'} : (term746 _86360) = (term764 _86360).
Proof. exact (MK_COMB (@lem3294685 _86360) (@lem3294689 _86360)). Qed.
Lemma lem3294691 {_86360 : Type'} : ((term745 _86360) = (term746 _86360)) = ((term744 _86360) = (term764 _86360)).
Proof. exact (MK_COMB (@lem3294679 _86360) (@lem3294690 _86360)). Qed.
Lemma lem3294692 {_86360 : Type'} : (term744 _86360) = (term764 _86360).
Proof. exact (EQ_MP (@lem3294691 _86360) (@lem3294669 _86360)). Qed.
Lemma lem3294805 {_86360 : Type'} : (term443 _86360) = (term764 _86360).
Proof. exact (TRANS (@lem3294665 _86360) (@lem3294692 _86360)). Qed.
Lemma lem3294806 {_86360 : Type'} : (term447 _86360) = (term765 _86360).
Proof. exact (MK_COMB (@lem3294396 _86360) (@lem3294805 _86360)). Qed.
Lemma lem3294807 {_86360 : Type'} : (term452 _86360) = (term766 _86360).
Proof. exact (MK_COMB (@lem3293830 _86360) (@lem3294806 _86360)). Qed.
Lemma lem3294808 {_86360 : Type'} : (term457 _86360) = (term767 _86360).
Proof. exact (MK_COMB (@lem3293264 _86360) (@lem3294807 _86360)). Qed.
Lemma lem3294810 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294811 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3294810 (_86360 -> Prop) P Q). Qed.
Lemma lem3294812 {_86360 : Type'} : (term507 _86360) = (term506 _86360).
Proof. exact (@lem3294811 _86360 (term508 _86360) (term509 _86360)). Qed.
Lemma lem3294813 {_86360 : Type'} (q : _86360 -> Prop) : (term510 _86360 q) = (term497 _86360 q).
Proof. exact (eq_refl (term510 _86360 q)). Qed.
Lemma lem3294814 {_86360 : Type'} : (term517 _86360) = (term508 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294813 _86360 q)). Qed.
Lemma lem3294815 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294816 {_86360 : Type'} : (term518 _86360) = (term519 _86360).
Proof. exact (MK_COMB (@lem3294815 _86360) (@lem3294814 _86360)). Qed.
Lemma lem3294817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294818 {_86360 : Type'} : (term520 _86360) = (term521 _86360).
Proof. exact (MK_COMB (@lem3294817) (@lem3294816 _86360)). Qed.
Lemma lem3294819 {_86360 : Type'} (q : _86360 -> Prop) : (term512 _86360 q) = (term502 _86360 q).
Proof. exact (eq_refl (term512 _86360 q)). Qed.
Lemma lem3294820 {_86360 : Type'} : (term522 _86360) = (term509 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294819 _86360 q)). Qed.
Lemma lem3294821 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294822 {_86360 : Type'} : (term523 _86360) = (term524 _86360).
Proof. exact (MK_COMB (@lem3294821 _86360) (@lem3294820 _86360)). Qed.
Lemma lem3294823 {_86360 : Type'} : (term507 _86360) = (term525 _86360).
Proof. exact (MK_COMB (@lem3294818 _86360) (@lem3294822 _86360)). Qed.
Lemma lem3294824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294825 {_86360 : Type'} : (term768 _86360) = (term769 _86360).
Proof. exact (MK_COMB (@lem3294824) (@lem3294823 _86360)). Qed.
Lemma lem3294826 {_86360 : Type'} (q : _86360 -> Prop) : (term510 _86360 q) = (term497 _86360 q).
Proof. exact (eq_refl (term510 _86360 q)). Qed.
Lemma lem3294827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294828 {_86360 : Type'} (q : _86360 -> Prop) : (term511 _86360 q) = (term499 _86360 q).
Proof. exact (MK_COMB (@lem3294827) (@lem3294826 _86360 q)). Qed.
Lemma lem3294829 {_86360 : Type'} (q : _86360 -> Prop) : (term512 _86360 q) = (term502 _86360 q).
Proof. exact (eq_refl (term512 _86360 q)). Qed.
Lemma lem3294830 {_86360 : Type'} (q : _86360 -> Prop) : (term513 _86360 q) = (term503 _86360 q).
Proof. exact (MK_COMB (@lem3294828 _86360 q) (@lem3294829 _86360 q)). Qed.
Lemma lem3294831 {_86360 : Type'} : (term514 _86360) = (term504 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294830 _86360 q)). Qed.
Lemma lem3294832 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294833 {_86360 : Type'} : (term506 _86360) = (term505 _86360).
Proof. exact (MK_COMB (@lem3294832 _86360) (@lem3294831 _86360)). Qed.
Lemma lem3294834 {_86360 : Type'} : ((term507 _86360) = (term506 _86360)) = ((term525 _86360) = (term505 _86360)).
Proof. exact (MK_COMB (@lem3294825 _86360) (@lem3294833 _86360)). Qed.
Lemma lem3294835 {_86360 : Type'} : (term525 _86360) = (term505 _86360).
Proof. exact (EQ_MP (@lem3294834 _86360) (@lem3294812 _86360)). Qed.
Lemma lem3294837 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294838 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3294837 (_86360 -> Prop) P Q). Qed.
Lemma lem3294839 {_86360 : Type'} (q : _86360 -> Prop) : (term485 _86360 q) = (term484 _86360 q).
Proof. exact (@lem3294838 _86360 (term486 _86360 q) (term487 _86360 q)). Qed.
Lemma lem3294840 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term488 _86360 q p) = (term473 _86360 q p).
Proof. exact (eq_refl (term488 _86360 q p)). Qed.
Lemma lem3294841 {_86360 : Type'} (q : _86360 -> Prop) : (term495 _86360 q) = (term486 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294840 _86360 q p)). Qed.
Lemma lem3294842 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294843 {_86360 : Type'} (q : _86360 -> Prop) : (term496 _86360 q) = (term497 _86360 q).
Proof. exact (MK_COMB (@lem3294842 _86360) (@lem3294841 _86360 q)). Qed.
Lemma lem3294844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294845 {_86360 : Type'} (q : _86360 -> Prop) : (term498 _86360 q) = (term499 _86360 q).
Proof. exact (MK_COMB (@lem3294844) (@lem3294843 _86360 q)). Qed.
Lemma lem3294846 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term490 _86360 q p) = (term478 _86360 q p).
Proof. exact (eq_refl (term490 _86360 q p)). Qed.
Lemma lem3294847 {_86360 : Type'} (q : _86360 -> Prop) : (term500 _86360 q) = (term487 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294846 _86360 q p)). Qed.
Lemma lem3294848 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294849 {_86360 : Type'} (q : _86360 -> Prop) : (term501 _86360 q) = (term502 _86360 q).
Proof. exact (MK_COMB (@lem3294848 _86360) (@lem3294847 _86360 q)). Qed.
Lemma lem3294850 {_86360 : Type'} (q : _86360 -> Prop) : (term485 _86360 q) = (term503 _86360 q).
Proof. exact (MK_COMB (@lem3294845 _86360 q) (@lem3294849 _86360 q)). Qed.
Lemma lem3294851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294852 {_86360 : Type'} (q : _86360 -> Prop) : (term770 _86360 q) = (term771 _86360 q).
Proof. exact (MK_COMB (@lem3294851) (@lem3294850 _86360 q)). Qed.
Lemma lem3294853 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term488 _86360 q p) = (term473 _86360 q p).
Proof. exact (eq_refl (term488 _86360 q p)). Qed.
Lemma lem3294854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294855 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term489 _86360 q p) = (term475 _86360 q p).
Proof. exact (MK_COMB (@lem3294854) (@lem3294853 _86360 q p)). Qed.
Lemma lem3294856 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term490 _86360 q p) = (term478 _86360 q p).
Proof. exact (eq_refl (term490 _86360 q p)). Qed.
Lemma lem3294857 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term491 _86360 q p) = (term479 _86360 q p).
Proof. exact (MK_COMB (@lem3294855 _86360 q p) (@lem3294856 _86360 q p)). Qed.
Lemma lem3294858 {_86360 : Type'} (q : _86360 -> Prop) : (term492 _86360 q) = (term480 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294857 _86360 q p)). Qed.
Lemma lem3294859 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294860 {_86360 : Type'} (q : _86360 -> Prop) : (term484 _86360 q) = (term481 _86360 q).
Proof. exact (MK_COMB (@lem3294859 _86360) (@lem3294858 _86360 q)). Qed.
Lemma lem3294861 {_86360 : Type'} (q : _86360 -> Prop) : ((term485 _86360 q) = (term484 _86360 q)) = ((term503 _86360 q) = (term481 _86360 q)).
Proof. exact (MK_COMB (@lem3294852 _86360 q) (@lem3294860 _86360 q)). Qed.
Lemma lem3294862 {_86360 : Type'} (q : _86360 -> Prop) : (term503 _86360 q) = (term481 _86360 q).
Proof. exact (EQ_MP (@lem3294861 _86360 q) (@lem3294839 _86360 q)). Qed.
Lemma lem3294864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294865 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term459 _86360 P Q) = (term458 _86360 P Q).
Proof. exact (@lem3294864 _86360 P Q). Qed.
Lemma lem3294866 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term461 _86360 q p) = (term460 _86360 q p).
Proof. exact (@lem3294865 _86360 (term462 _86360 q p) (term463 _86360 q p)). Qed.
Lemma lem3294867 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term464 _86360 q p x) = (term297 _86360 q p x).
Proof. exact (eq_refl (term464 _86360 q p x)). Qed.
Lemma lem3294868 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term471 _86360 q p) = (term462 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3294867 _86360 q p x)). Qed.
Lemma lem3294869 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294870 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term472 _86360 q p) = (term473 _86360 q p).
Proof. exact (MK_COMB (@lem3294869 _86360) (@lem3294868 _86360 q p)). Qed.
Lemma lem3294871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294872 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term474 _86360 q p) = (term475 _86360 q p).
Proof. exact (MK_COMB (@lem3294871) (@lem3294870 _86360 q p)). Qed.
Lemma lem3294873 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term466 _86360 q p x) = (term295 _86360 q p x).
Proof. exact (eq_refl (term466 _86360 q p x)). Qed.
Lemma lem3294874 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term476 _86360 q p) = (term463 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3294873 _86360 q p x)). Qed.
Lemma lem3294875 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294876 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term477 _86360 q p) = (term478 _86360 q p).
Proof. exact (MK_COMB (@lem3294875 _86360) (@lem3294874 _86360 q p)). Qed.
Lemma lem3294877 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term461 _86360 q p) = (term479 _86360 q p).
Proof. exact (MK_COMB (@lem3294872 _86360 q p) (@lem3294876 _86360 q p)). Qed.
Lemma lem3294878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294879 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term772 _86360 q p) = (term773 _86360 q p).
Proof. exact (MK_COMB (@lem3294878) (@lem3294877 _86360 q p)). Qed.
Lemma lem3294880 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term464 _86360 q p x) = (term297 _86360 q p x).
Proof. exact (eq_refl (term464 _86360 q p x)). Qed.
Lemma lem3294881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294882 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term465 _86360 q p x) = (term299 _86360 q p x).
Proof. exact (MK_COMB (@lem3294881) (@lem3294880 _86360 q p x)). Qed.
Lemma lem3294883 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term466 _86360 q p x) = (term295 _86360 q p x).
Proof. exact (eq_refl (term466 _86360 q p x)). Qed.
Lemma lem3294884 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term467 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (MK_COMB (@lem3294882 _86360 q p x) (@lem3294883 _86360 q p x)). Qed.
Lemma lem3294885 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term468 _86360 q p) = (term310 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3294884 _86360 q p x)). Qed.
Lemma lem3294886 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294887 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term460 _86360 q p) = (term311 _86360 q p).
Proof. exact (MK_COMB (@lem3294886 _86360) (@lem3294885 _86360 q p)). Qed.
Lemma lem3294888 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : ((term461 _86360 q p) = (term460 _86360 q p)) = ((term479 _86360 q p) = (term311 _86360 q p)).
Proof. exact (MK_COMB (@lem3294879 _86360 q p) (@lem3294887 _86360 q p)). Qed.
Lemma lem3294889 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term479 _86360 q p) = (term311 _86360 q p).
Proof. exact (EQ_MP (@lem3294888 _86360 q p) (@lem3294866 _86360 q p)). Qed.
Lemma lem3294890 {_86360 : Type'} (q : _86360 -> Prop) : (term480 _86360 q) = (term318 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294889 _86360 q p)). Qed.
Lemma lem3294891 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294892 {_86360 : Type'} (q : _86360 -> Prop) : (term481 _86360 q) = (term319 _86360 q).
Proof. exact (MK_COMB (@lem3294891 _86360) (@lem3294890 _86360 q)). Qed.
Lemma lem3294893 {_86360 : Type'} (q : _86360 -> Prop) : (term503 _86360 q) = (term319 _86360 q).
Proof. exact (TRANS (@lem3294862 _86360 q) (@lem3294892 _86360 q)). Qed.
Lemma lem3294894 {_86360 : Type'} : (term504 _86360) = (term324 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294893 _86360 q)). Qed.
Lemma lem3294895 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294896 {_86360 : Type'} : (term505 _86360) = (term325 _86360).
Proof. exact (MK_COMB (@lem3294895 _86360) (@lem3294894 _86360)). Qed.
Lemma lem3294897 {_86360 : Type'} : (term525 _86360) = (term325 _86360).
Proof. exact (TRANS (@lem3294835 _86360) (@lem3294896 _86360)). Qed.
Lemma lem3294898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294899 {_86360 : Type'} : (term526 _86360) = (term455 _86360).
Proof. exact (MK_COMB (@lem3294898) (@lem3294897 _86360)). Qed.
Lemma lem3294901 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294902 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3294901 (_86360 -> Prop) P Q). Qed.
Lemma lem3294903 {_86360 : Type'} : (term594 _86360) = (term593 _86360).
Proof. exact (@lem3294902 _86360 (term595 _86360) (term596 _86360)). Qed.
Lemma lem3294904 {_86360 : Type'} (q : _86360 -> Prop) : (term597 _86360 q) = (term584 _86360 q).
Proof. exact (eq_refl (term597 _86360 q)). Qed.
Lemma lem3294905 {_86360 : Type'} : (term604 _86360) = (term595 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294904 _86360 q)). Qed.
Lemma lem3294906 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294907 {_86360 : Type'} : (term605 _86360) = (term606 _86360).
Proof. exact (MK_COMB (@lem3294906 _86360) (@lem3294905 _86360)). Qed.
Lemma lem3294908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294909 {_86360 : Type'} : (term607 _86360) = (term608 _86360).
Proof. exact (MK_COMB (@lem3294908) (@lem3294907 _86360)). Qed.
Lemma lem3294910 {_86360 : Type'} (q : _86360 -> Prop) : (term599 _86360 q) = (term589 _86360 q).
Proof. exact (eq_refl (term599 _86360 q)). Qed.
Lemma lem3294911 {_86360 : Type'} : (term609 _86360) = (term596 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294910 _86360 q)). Qed.
Lemma lem3294912 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294913 {_86360 : Type'} : (term610 _86360) = (term611 _86360).
Proof. exact (MK_COMB (@lem3294912 _86360) (@lem3294911 _86360)). Qed.
Lemma lem3294914 {_86360 : Type'} : (term594 _86360) = (term612 _86360).
Proof. exact (MK_COMB (@lem3294909 _86360) (@lem3294913 _86360)). Qed.
Lemma lem3294915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294916 {_86360 : Type'} : (term774 _86360) = (term775 _86360).
Proof. exact (MK_COMB (@lem3294915) (@lem3294914 _86360)). Qed.
Lemma lem3294917 {_86360 : Type'} (q : _86360 -> Prop) : (term597 _86360 q) = (term584 _86360 q).
Proof. exact (eq_refl (term597 _86360 q)). Qed.
Lemma lem3294918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294919 {_86360 : Type'} (q : _86360 -> Prop) : (term598 _86360 q) = (term586 _86360 q).
Proof. exact (MK_COMB (@lem3294918) (@lem3294917 _86360 q)). Qed.
Lemma lem3294920 {_86360 : Type'} (q : _86360 -> Prop) : (term599 _86360 q) = (term589 _86360 q).
Proof. exact (eq_refl (term599 _86360 q)). Qed.
Lemma lem3294921 {_86360 : Type'} (q : _86360 -> Prop) : (term600 _86360 q) = (term590 _86360 q).
Proof. exact (MK_COMB (@lem3294919 _86360 q) (@lem3294920 _86360 q)). Qed.
Lemma lem3294922 {_86360 : Type'} : (term601 _86360) = (term591 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3294921 _86360 q)). Qed.
Lemma lem3294923 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294924 {_86360 : Type'} : (term593 _86360) = (term592 _86360).
Proof. exact (MK_COMB (@lem3294923 _86360) (@lem3294922 _86360)). Qed.
Lemma lem3294925 {_86360 : Type'} : ((term594 _86360) = (term593 _86360)) = ((term612 _86360) = (term592 _86360)).
Proof. exact (MK_COMB (@lem3294916 _86360) (@lem3294924 _86360)). Qed.
Lemma lem3294926 {_86360 : Type'} : (term612 _86360) = (term592 _86360).
Proof. exact (EQ_MP (@lem3294925 _86360) (@lem3294903 _86360)). Qed.
Lemma lem3294928 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294929 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3294928 (_86360 -> Prop) P Q). Qed.
Lemma lem3294930 {_86360 : Type'} (q : _86360 -> Prop) : (term572 _86360 q) = (term571 _86360 q).
Proof. exact (@lem3294929 _86360 (term573 _86360 q) (term574 _86360 q)). Qed.
Lemma lem3294931 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term575 _86360 q p) = (term562 _86360 p q).
Proof. exact (eq_refl (term575 _86360 q p)). Qed.
Lemma lem3294932 {_86360 : Type'} (q : _86360 -> Prop) : (term582 _86360 q) = (term573 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294931 _86360 p q)). Qed.
Lemma lem3294933 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294934 {_86360 : Type'} (q : _86360 -> Prop) : (term583 _86360 q) = (term584 _86360 q).
Proof. exact (MK_COMB (@lem3294933 _86360) (@lem3294932 _86360 q)). Qed.
Lemma lem3294935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294936 {_86360 : Type'} (q : _86360 -> Prop) : (term585 _86360 q) = (term586 _86360 q).
Proof. exact (MK_COMB (@lem3294935) (@lem3294934 _86360 q)). Qed.
Lemma lem3294937 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term577 _86360 q p) = (term567 _86360 p q).
Proof. exact (eq_refl (term577 _86360 q p)). Qed.
Lemma lem3294938 {_86360 : Type'} (q : _86360 -> Prop) : (term587 _86360 q) = (term574 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294937 _86360 p q)). Qed.
Lemma lem3294939 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294940 {_86360 : Type'} (q : _86360 -> Prop) : (term588 _86360 q) = (term589 _86360 q).
Proof. exact (MK_COMB (@lem3294939 _86360) (@lem3294938 _86360 q)). Qed.
Lemma lem3294941 {_86360 : Type'} (q : _86360 -> Prop) : (term572 _86360 q) = (term590 _86360 q).
Proof. exact (MK_COMB (@lem3294936 _86360 q) (@lem3294940 _86360 q)). Qed.
Lemma lem3294942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294943 {_86360 : Type'} (q : _86360 -> Prop) : (term776 _86360 q) = (term777 _86360 q).
Proof. exact (MK_COMB (@lem3294942) (@lem3294941 _86360 q)). Qed.
Lemma lem3294944 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term575 _86360 q p) = (term562 _86360 p q).
Proof. exact (eq_refl (term575 _86360 q p)). Qed.
Lemma lem3294945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294946 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term576 _86360 q p) = (term564 _86360 p q).
Proof. exact (MK_COMB (@lem3294945) (@lem3294944 _86360 p q)). Qed.
Lemma lem3294947 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term577 _86360 q p) = (term567 _86360 p q).
Proof. exact (eq_refl (term577 _86360 q p)). Qed.
Lemma lem3294948 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term578 _86360 q p) = (term568 _86360 p q).
Proof. exact (MK_COMB (@lem3294946 _86360 p q) (@lem3294947 _86360 p q)). Qed.
Lemma lem3294949 {_86360 : Type'} (q : _86360 -> Prop) : (term579 _86360 q) = (term569 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3294948 _86360 p q)). Qed.
Lemma lem3294950 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294951 {_86360 : Type'} (q : _86360 -> Prop) : (term571 _86360 q) = (term570 _86360 q).
Proof. exact (MK_COMB (@lem3294950 _86360) (@lem3294949 _86360 q)). Qed.
Lemma lem3294952 {_86360 : Type'} (q : _86360 -> Prop) : ((term572 _86360 q) = (term571 _86360 q)) = ((term590 _86360 q) = (term570 _86360 q)).
Proof. exact (MK_COMB (@lem3294943 _86360 q) (@lem3294951 _86360 q)). Qed.
Lemma lem3294953 {_86360 : Type'} (q : _86360 -> Prop) : (term590 _86360 q) = (term570 _86360 q).
Proof. exact (EQ_MP (@lem3294952 _86360 q) (@lem3294930 _86360 q)). Qed.
Lemma lem3294955 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294956 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3294955 (_86360 -> Prop) P Q). Qed.
Lemma lem3294957 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term550 _86360 p q) = (term549 _86360 p q).
Proof. exact (@lem3294956 _86360 (term551 _86360 p q) (term552 _86360 p q)). Qed.
Lemma lem3294958 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term553 _86360 p q r) = (term540 _86360 p q r).
Proof. exact (eq_refl (term553 _86360 p q r)). Qed.
Lemma lem3294959 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term560 _86360 p q) = (term551 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3294958 _86360 p q r)). Qed.
Lemma lem3294960 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294961 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term561 _86360 p q) = (term562 _86360 p q).
Proof. exact (MK_COMB (@lem3294960 _86360) (@lem3294959 _86360 p q)). Qed.
Lemma lem3294962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294963 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term563 _86360 p q) = (term564 _86360 p q).
Proof. exact (MK_COMB (@lem3294962) (@lem3294961 _86360 p q)). Qed.
Lemma lem3294964 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term555 _86360 p q r) = (term545 _86360 p q r).
Proof. exact (eq_refl (term555 _86360 p q r)). Qed.
Lemma lem3294965 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term565 _86360 p q) = (term552 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3294964 _86360 p q r)). Qed.
Lemma lem3294966 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294967 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term566 _86360 p q) = (term567 _86360 p q).
Proof. exact (MK_COMB (@lem3294966 _86360) (@lem3294965 _86360 p q)). Qed.
Lemma lem3294968 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term550 _86360 p q) = (term568 _86360 p q).
Proof. exact (MK_COMB (@lem3294963 _86360 p q) (@lem3294967 _86360 p q)). Qed.
Lemma lem3294969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294970 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term778 _86360 p q) = (term779 _86360 p q).
Proof. exact (MK_COMB (@lem3294969) (@lem3294968 _86360 p q)). Qed.
Lemma lem3294971 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term553 _86360 p q r) = (term540 _86360 p q r).
Proof. exact (eq_refl (term553 _86360 p q r)). Qed.
Lemma lem3294972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294973 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term554 _86360 p q r) = (term542 _86360 p q r).
Proof. exact (MK_COMB (@lem3294972) (@lem3294971 _86360 p q r)). Qed.
Lemma lem3294974 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term555 _86360 p q r) = (term545 _86360 p q r).
Proof. exact (eq_refl (term555 _86360 p q r)). Qed.
Lemma lem3294975 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term556 _86360 p q r) = (term546 _86360 p q r).
Proof. exact (MK_COMB (@lem3294973 _86360 p q r) (@lem3294974 _86360 p q r)). Qed.
Lemma lem3294976 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term557 _86360 p q) = (term547 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3294975 _86360 p q r)). Qed.
Lemma lem3294977 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3294978 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term549 _86360 p q) = (term548 _86360 p q).
Proof. exact (MK_COMB (@lem3294977 _86360) (@lem3294976 _86360 p q)). Qed.
Lemma lem3294979 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term550 _86360 p q) = (term549 _86360 p q)) = ((term568 _86360 p q) = (term548 _86360 p q)).
Proof. exact (MK_COMB (@lem3294970 _86360 p q) (@lem3294978 _86360 p q)). Qed.
Lemma lem3294980 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term568 _86360 p q) = (term548 _86360 p q).
Proof. exact (EQ_MP (@lem3294979 _86360 p q) (@lem3294957 _86360 p q)). Qed.
Lemma lem3294982 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3294983 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term459 _86360 P Q) = (term458 _86360 P Q).
Proof. exact (@lem3294982 _86360 P Q). Qed.
Lemma lem3294984 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term528 _86360 p q r) = (term527 _86360 p q r).
Proof. exact (@lem3294983 _86360 (term529 _86360 p q r) (term530 _86360 p q r)). Qed.
Lemma lem3294985 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term531 _86360 p q r x) = (term342 _86360 p q r x).
Proof. exact (eq_refl (term531 _86360 p q r x)). Qed.
Lemma lem3294986 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term538 _86360 p q r) = (term529 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3294985 _86360 p q r x)). Qed.
Lemma lem3294987 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294988 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term539 _86360 p q r) = (term540 _86360 p q r).
Proof. exact (MK_COMB (@lem3294987 _86360) (@lem3294986 _86360 p q r)). Qed.
Lemma lem3294989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3294990 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term541 _86360 p q r) = (term542 _86360 p q r).
Proof. exact (MK_COMB (@lem3294989) (@lem3294988 _86360 p q r)). Qed.
Lemma lem3294991 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term533 _86360 p q r x) = (term339 _86360 p q r x).
Proof. exact (eq_refl (term533 _86360 p q r x)). Qed.
Lemma lem3294992 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term543 _86360 p q r) = (term530 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3294991 _86360 p q r x)). Qed.
Lemma lem3294993 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3294994 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term544 _86360 p q r) = (term545 _86360 p q r).
Proof. exact (MK_COMB (@lem3294993 _86360) (@lem3294992 _86360 p q r)). Qed.
Lemma lem3294995 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term528 _86360 p q r) = (term546 _86360 p q r).
Proof. exact (MK_COMB (@lem3294990 _86360 p q r) (@lem3294994 _86360 p q r)). Qed.
Lemma lem3294996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3294997 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term780 _86360 p q r) = (term781 _86360 p q r).
Proof. exact (MK_COMB (@lem3294996) (@lem3294995 _86360 p q r)). Qed.
Lemma lem3294998 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term531 _86360 p q r x) = (term342 _86360 p q r x).
Proof. exact (eq_refl (term531 _86360 p q r x)). Qed.
Lemma lem3294999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295000 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term532 _86360 p q r x) = (term344 _86360 p q r x).
Proof. exact (MK_COMB (@lem3294999) (@lem3294998 _86360 p q r x)). Qed.
Lemma lem3295001 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term533 _86360 p q r x) = (term339 _86360 p q r x).
Proof. exact (eq_refl (term533 _86360 p q r x)). Qed.
Lemma lem3295002 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term534 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (MK_COMB (@lem3295000 _86360 p q r x) (@lem3295001 _86360 p q r x)). Qed.
Lemma lem3295003 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term535 _86360 p q r) = (term353 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3295002 _86360 p q r x)). Qed.
Lemma lem3295004 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295005 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term527 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (MK_COMB (@lem3295004 _86360) (@lem3295003 _86360 p q r)). Qed.
Lemma lem3295006 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : ((term528 _86360 p q r) = (term527 _86360 p q r)) = ((term546 _86360 p q r) = (term354 _86360 p q r)).
Proof. exact (MK_COMB (@lem3294997 _86360 p q r) (@lem3295005 _86360 p q r)). Qed.
Lemma lem3295007 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term546 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (EQ_MP (@lem3295006 _86360 p q r) (@lem3294984 _86360 p q r)). Qed.
Lemma lem3295008 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term547 _86360 p q) = (term359 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295007 _86360 p q r)). Qed.
Lemma lem3295009 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295010 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term548 _86360 p q) = (term360 _86360 p q).
Proof. exact (MK_COMB (@lem3295009 _86360) (@lem3295008 _86360 p q)). Qed.
Lemma lem3295011 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term568 _86360 p q) = (term360 _86360 p q).
Proof. exact (TRANS (@lem3294980 _86360 p q) (@lem3295010 _86360 p q)). Qed.
Lemma lem3295012 {_86360 : Type'} (q : _86360 -> Prop) : (term569 _86360 q) = (term365 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295011 _86360 p q)). Qed.
Lemma lem3295013 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295014 {_86360 : Type'} (q : _86360 -> Prop) : (term570 _86360 q) = (term366 _86360 q).
Proof. exact (MK_COMB (@lem3295013 _86360) (@lem3295012 _86360 q)). Qed.
Lemma lem3295015 {_86360 : Type'} (q : _86360 -> Prop) : (term590 _86360 q) = (term366 _86360 q).
Proof. exact (TRANS (@lem3294953 _86360 q) (@lem3295014 _86360 q)). Qed.
Lemma lem3295016 {_86360 : Type'} : (term591 _86360) = (term371 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295015 _86360 q)). Qed.
Lemma lem3295017 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295018 {_86360 : Type'} : (term592 _86360) = (term372 _86360).
Proof. exact (MK_COMB (@lem3295017 _86360) (@lem3295016 _86360)). Qed.
Lemma lem3295019 {_86360 : Type'} : (term612 _86360) = (term372 _86360).
Proof. exact (TRANS (@lem3294926 _86360) (@lem3295018 _86360)). Qed.
Lemma lem3295020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295021 {_86360 : Type'} : (term613 _86360) = (term450 _86360).
Proof. exact (MK_COMB (@lem3295020) (@lem3295019 _86360)). Qed.
Lemma lem3295023 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295024 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295023 (_86360 -> Prop) P Q). Qed.
Lemma lem3295025 {_86360 : Type'} : (term681 _86360) = (term680 _86360).
Proof. exact (@lem3295024 _86360 (term682 _86360) (term683 _86360)). Qed.
Lemma lem3295026 {_86360 : Type'} (q : _86360 -> Prop) : (term684 _86360 q) = (term671 _86360 q).
Proof. exact (eq_refl (term684 _86360 q)). Qed.
Lemma lem3295027 {_86360 : Type'} : (term691 _86360) = (term682 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295026 _86360 q)). Qed.
Lemma lem3295028 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295029 {_86360 : Type'} : (term692 _86360) = (term693 _86360).
Proof. exact (MK_COMB (@lem3295028 _86360) (@lem3295027 _86360)). Qed.
Lemma lem3295030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295031 {_86360 : Type'} : (term694 _86360) = (term695 _86360).
Proof. exact (MK_COMB (@lem3295030) (@lem3295029 _86360)). Qed.
Lemma lem3295032 {_86360 : Type'} (q : _86360 -> Prop) : (term686 _86360 q) = (term676 _86360 q).
Proof. exact (eq_refl (term686 _86360 q)). Qed.
Lemma lem3295033 {_86360 : Type'} : (term696 _86360) = (term683 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295032 _86360 q)). Qed.
Lemma lem3295034 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295035 {_86360 : Type'} : (term697 _86360) = (term698 _86360).
Proof. exact (MK_COMB (@lem3295034 _86360) (@lem3295033 _86360)). Qed.
Lemma lem3295036 {_86360 : Type'} : (term681 _86360) = (term699 _86360).
Proof. exact (MK_COMB (@lem3295031 _86360) (@lem3295035 _86360)). Qed.
Lemma lem3295037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295038 {_86360 : Type'} : (term782 _86360) = (term783 _86360).
Proof. exact (MK_COMB (@lem3295037) (@lem3295036 _86360)). Qed.
Lemma lem3295039 {_86360 : Type'} (q : _86360 -> Prop) : (term684 _86360 q) = (term671 _86360 q).
Proof. exact (eq_refl (term684 _86360 q)). Qed.
Lemma lem3295040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295041 {_86360 : Type'} (q : _86360 -> Prop) : (term685 _86360 q) = (term673 _86360 q).
Proof. exact (MK_COMB (@lem3295040) (@lem3295039 _86360 q)). Qed.
Lemma lem3295042 {_86360 : Type'} (q : _86360 -> Prop) : (term686 _86360 q) = (term676 _86360 q).
Proof. exact (eq_refl (term686 _86360 q)). Qed.
Lemma lem3295043 {_86360 : Type'} (q : _86360 -> Prop) : (term687 _86360 q) = (term677 _86360 q).
Proof. exact (MK_COMB (@lem3295041 _86360 q) (@lem3295042 _86360 q)). Qed.
Lemma lem3295044 {_86360 : Type'} : (term688 _86360) = (term678 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295043 _86360 q)). Qed.
Lemma lem3295045 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295046 {_86360 : Type'} : (term680 _86360) = (term679 _86360).
Proof. exact (MK_COMB (@lem3295045 _86360) (@lem3295044 _86360)). Qed.
Lemma lem3295047 {_86360 : Type'} : ((term681 _86360) = (term680 _86360)) = ((term699 _86360) = (term679 _86360)).
Proof. exact (MK_COMB (@lem3295038 _86360) (@lem3295046 _86360)). Qed.
Lemma lem3295048 {_86360 : Type'} : (term699 _86360) = (term679 _86360).
Proof. exact (EQ_MP (@lem3295047 _86360) (@lem3295025 _86360)). Qed.
Lemma lem3295050 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295051 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295050 (_86360 -> Prop) P Q). Qed.
Lemma lem3295052 {_86360 : Type'} (q : _86360 -> Prop) : (term659 _86360 q) = (term658 _86360 q).
Proof. exact (@lem3295051 _86360 (term660 _86360 q) (term661 _86360 q)). Qed.
Lemma lem3295053 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term662 _86360 q p) = (term649 _86360 q p).
Proof. exact (eq_refl (term662 _86360 q p)). Qed.
Lemma lem3295054 {_86360 : Type'} (q : _86360 -> Prop) : (term669 _86360 q) = (term660 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295053 _86360 q p)). Qed.
Lemma lem3295055 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295056 {_86360 : Type'} (q : _86360 -> Prop) : (term670 _86360 q) = (term671 _86360 q).
Proof. exact (MK_COMB (@lem3295055 _86360) (@lem3295054 _86360 q)). Qed.
Lemma lem3295057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295058 {_86360 : Type'} (q : _86360 -> Prop) : (term672 _86360 q) = (term673 _86360 q).
Proof. exact (MK_COMB (@lem3295057) (@lem3295056 _86360 q)). Qed.
Lemma lem3295059 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term664 _86360 q p) = (term654 _86360 q p).
Proof. exact (eq_refl (term664 _86360 q p)). Qed.
Lemma lem3295060 {_86360 : Type'} (q : _86360 -> Prop) : (term674 _86360 q) = (term661 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295059 _86360 q p)). Qed.
Lemma lem3295061 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295062 {_86360 : Type'} (q : _86360 -> Prop) : (term675 _86360 q) = (term676 _86360 q).
Proof. exact (MK_COMB (@lem3295061 _86360) (@lem3295060 _86360 q)). Qed.
Lemma lem3295063 {_86360 : Type'} (q : _86360 -> Prop) : (term659 _86360 q) = (term677 _86360 q).
Proof. exact (MK_COMB (@lem3295058 _86360 q) (@lem3295062 _86360 q)). Qed.
Lemma lem3295064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295065 {_86360 : Type'} (q : _86360 -> Prop) : (term784 _86360 q) = (term785 _86360 q).
Proof. exact (MK_COMB (@lem3295064) (@lem3295063 _86360 q)). Qed.
Lemma lem3295066 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term662 _86360 q p) = (term649 _86360 q p).
Proof. exact (eq_refl (term662 _86360 q p)). Qed.
Lemma lem3295067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295068 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term663 _86360 q p) = (term651 _86360 q p).
Proof. exact (MK_COMB (@lem3295067) (@lem3295066 _86360 q p)). Qed.
Lemma lem3295069 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term664 _86360 q p) = (term654 _86360 q p).
Proof. exact (eq_refl (term664 _86360 q p)). Qed.
Lemma lem3295070 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term665 _86360 q p) = (term655 _86360 q p).
Proof. exact (MK_COMB (@lem3295068 _86360 q p) (@lem3295069 _86360 q p)). Qed.
Lemma lem3295071 {_86360 : Type'} (q : _86360 -> Prop) : (term666 _86360 q) = (term656 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295070 _86360 q p)). Qed.
Lemma lem3295072 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295073 {_86360 : Type'} (q : _86360 -> Prop) : (term658 _86360 q) = (term657 _86360 q).
Proof. exact (MK_COMB (@lem3295072 _86360) (@lem3295071 _86360 q)). Qed.
Lemma lem3295074 {_86360 : Type'} (q : _86360 -> Prop) : ((term659 _86360 q) = (term658 _86360 q)) = ((term677 _86360 q) = (term657 _86360 q)).
Proof. exact (MK_COMB (@lem3295065 _86360 q) (@lem3295073 _86360 q)). Qed.
Lemma lem3295075 {_86360 : Type'} (q : _86360 -> Prop) : (term677 _86360 q) = (term657 _86360 q).
Proof. exact (EQ_MP (@lem3295074 _86360 q) (@lem3295052 _86360 q)). Qed.
Lemma lem3295077 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295078 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295077 (_86360 -> Prop) P Q). Qed.
Lemma lem3295079 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term637 _86360 q p) = (term636 _86360 q p).
Proof. exact (@lem3295078 _86360 (term638 _86360 q p) (term639 _86360 q p)). Qed.
Lemma lem3295080 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term640 _86360 q p r) = (term627 _86360 q p r).
Proof. exact (eq_refl (term640 _86360 q p r)). Qed.
Lemma lem3295081 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term647 _86360 q p) = (term638 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295080 _86360 q p r)). Qed.
Lemma lem3295082 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295083 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term648 _86360 q p) = (term649 _86360 q p).
Proof. exact (MK_COMB (@lem3295082 _86360) (@lem3295081 _86360 q p)). Qed.
Lemma lem3295084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295085 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term650 _86360 q p) = (term651 _86360 q p).
Proof. exact (MK_COMB (@lem3295084) (@lem3295083 _86360 q p)). Qed.
Lemma lem3295086 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term642 _86360 q p r) = (term632 _86360 q p r).
Proof. exact (eq_refl (term642 _86360 q p r)). Qed.
Lemma lem3295087 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term652 _86360 q p) = (term639 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295086 _86360 q p r)). Qed.
Lemma lem3295088 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295089 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term653 _86360 q p) = (term654 _86360 q p).
Proof. exact (MK_COMB (@lem3295088 _86360) (@lem3295087 _86360 q p)). Qed.
Lemma lem3295090 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term637 _86360 q p) = (term655 _86360 q p).
Proof. exact (MK_COMB (@lem3295085 _86360 q p) (@lem3295089 _86360 q p)). Qed.
Lemma lem3295091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295092 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term786 _86360 q p) = (term787 _86360 q p).
Proof. exact (MK_COMB (@lem3295091) (@lem3295090 _86360 q p)). Qed.
Lemma lem3295093 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term640 _86360 q p r) = (term627 _86360 q p r).
Proof. exact (eq_refl (term640 _86360 q p r)). Qed.
Lemma lem3295094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295095 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term641 _86360 q p r) = (term629 _86360 q p r).
Proof. exact (MK_COMB (@lem3295094) (@lem3295093 _86360 q p r)). Qed.
Lemma lem3295096 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term642 _86360 q p r) = (term632 _86360 q p r).
Proof. exact (eq_refl (term642 _86360 q p r)). Qed.
Lemma lem3295097 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term643 _86360 q p r) = (term633 _86360 q p r).
Proof. exact (MK_COMB (@lem3295095 _86360 q p r) (@lem3295096 _86360 q p r)). Qed.
Lemma lem3295098 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term644 _86360 q p) = (term634 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295097 _86360 q p r)). Qed.
Lemma lem3295099 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295100 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term636 _86360 q p) = (term635 _86360 q p).
Proof. exact (MK_COMB (@lem3295099 _86360) (@lem3295098 _86360 q p)). Qed.
Lemma lem3295101 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : ((term637 _86360 q p) = (term636 _86360 q p)) = ((term655 _86360 q p) = (term635 _86360 q p)).
Proof. exact (MK_COMB (@lem3295092 _86360 q p) (@lem3295100 _86360 q p)). Qed.
Lemma lem3295102 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term655 _86360 q p) = (term635 _86360 q p).
Proof. exact (EQ_MP (@lem3295101 _86360 q p) (@lem3295079 _86360 q p)). Qed.
Lemma lem3295104 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295105 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term459 _86360 P Q) = (term458 _86360 P Q).
Proof. exact (@lem3295104 _86360 P Q). Qed.
Lemma lem3295106 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term615 _86360 q p r) = (term614 _86360 q p r).
Proof. exact (@lem3295105 _86360 (term616 _86360 q p r) (term617 _86360 q p r)). Qed.
Lemma lem3295107 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term618 _86360 q p r x) = (term379 _86360 q p r x).
Proof. exact (eq_refl (term618 _86360 q p r x)). Qed.
Lemma lem3295108 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term625 _86360 q p r) = (term616 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3295107 _86360 q p r x)). Qed.
Lemma lem3295109 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295110 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term626 _86360 q p r) = (term627 _86360 q p r).
Proof. exact (MK_COMB (@lem3295109 _86360) (@lem3295108 _86360 q p r)). Qed.
Lemma lem3295111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295112 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term628 _86360 q p r) = (term629 _86360 q p r).
Proof. exact (MK_COMB (@lem3295111) (@lem3295110 _86360 q p r)). Qed.
Lemma lem3295113 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term620 _86360 q p r x) = (term376 _86360 q p r x).
Proof. exact (eq_refl (term620 _86360 q p r x)). Qed.
Lemma lem3295114 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term630 _86360 q p r) = (term617 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3295113 _86360 q p r x)). Qed.
Lemma lem3295115 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295116 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term631 _86360 q p r) = (term632 _86360 q p r).
Proof. exact (MK_COMB (@lem3295115 _86360) (@lem3295114 _86360 q p r)). Qed.
Lemma lem3295117 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term615 _86360 q p r) = (term633 _86360 q p r).
Proof. exact (MK_COMB (@lem3295112 _86360 q p r) (@lem3295116 _86360 q p r)). Qed.
Lemma lem3295118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295119 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term788 _86360 q p r) = (term789 _86360 q p r).
Proof. exact (MK_COMB (@lem3295118) (@lem3295117 _86360 q p r)). Qed.
Lemma lem3295120 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term618 _86360 q p r x) = (term379 _86360 q p r x).
Proof. exact (eq_refl (term618 _86360 q p r x)). Qed.
Lemma lem3295121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295122 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term619 _86360 q p r x) = (term381 _86360 q p r x).
Proof. exact (MK_COMB (@lem3295121) (@lem3295120 _86360 q p r x)). Qed.
Lemma lem3295123 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term620 _86360 q p r x) = (term376 _86360 q p r x).
Proof. exact (eq_refl (term620 _86360 q p r x)). Qed.
Lemma lem3295124 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term621 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (MK_COMB (@lem3295122 _86360 q p r x) (@lem3295123 _86360 q p r x)). Qed.
Lemma lem3295125 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term622 _86360 q p r) = (term390 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3295124 _86360 q p r x)). Qed.
Lemma lem3295126 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295127 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term614 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (MK_COMB (@lem3295126 _86360) (@lem3295125 _86360 q p r)). Qed.
Lemma lem3295128 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : ((term615 _86360 q p r) = (term614 _86360 q p r)) = ((term633 _86360 q p r) = (term391 _86360 q p r)).
Proof. exact (MK_COMB (@lem3295119 _86360 q p r) (@lem3295127 _86360 q p r)). Qed.
Lemma lem3295129 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term633 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (EQ_MP (@lem3295128 _86360 q p r) (@lem3295106 _86360 q p r)). Qed.
Lemma lem3295130 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term634 _86360 q p) = (term396 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295129 _86360 q p r)). Qed.
Lemma lem3295131 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295132 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term635 _86360 q p) = (term397 _86360 q p).
Proof. exact (MK_COMB (@lem3295131 _86360) (@lem3295130 _86360 q p)). Qed.
Lemma lem3295133 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term655 _86360 q p) = (term397 _86360 q p).
Proof. exact (TRANS (@lem3295102 _86360 q p) (@lem3295132 _86360 q p)). Qed.
Lemma lem3295134 {_86360 : Type'} (q : _86360 -> Prop) : (term656 _86360 q) = (term402 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295133 _86360 q p)). Qed.
Lemma lem3295135 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295136 {_86360 : Type'} (q : _86360 -> Prop) : (term657 _86360 q) = (term403 _86360 q).
Proof. exact (MK_COMB (@lem3295135 _86360) (@lem3295134 _86360 q)). Qed.
Lemma lem3295137 {_86360 : Type'} (q : _86360 -> Prop) : (term677 _86360 q) = (term403 _86360 q).
Proof. exact (TRANS (@lem3295075 _86360 q) (@lem3295136 _86360 q)). Qed.
Lemma lem3295138 {_86360 : Type'} : (term678 _86360) = (term408 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295137 _86360 q)). Qed.
Lemma lem3295139 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295140 {_86360 : Type'} : (term679 _86360) = (term409 _86360).
Proof. exact (MK_COMB (@lem3295139 _86360) (@lem3295138 _86360)). Qed.
Lemma lem3295141 {_86360 : Type'} : (term699 _86360) = (term409 _86360).
Proof. exact (TRANS (@lem3295048 _86360) (@lem3295140 _86360)). Qed.
Lemma lem3295142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295143 {_86360 : Type'} : (term700 _86360) = (term445 _86360).
Proof. exact (MK_COMB (@lem3295142) (@lem3295141 _86360)). Qed.
Lemma lem3295145 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295146 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295145 (_86360 -> Prop) P Q). Qed.
Lemma lem3295147 {_86360 : Type'} : (term746 _86360) = (term745 _86360).
Proof. exact (@lem3295146 _86360 (term747 _86360) (term748 _86360)). Qed.
Lemma lem3295148 {_86360 : Type'} (q : _86360 -> Prop) : (term749 _86360 q) = (term736 _86360 q).
Proof. exact (eq_refl (term749 _86360 q)). Qed.
Lemma lem3295149 {_86360 : Type'} : (term756 _86360) = (term747 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295148 _86360 q)). Qed.
Lemma lem3295150 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295151 {_86360 : Type'} : (term757 _86360) = (term758 _86360).
Proof. exact (MK_COMB (@lem3295150 _86360) (@lem3295149 _86360)). Qed.
Lemma lem3295152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295153 {_86360 : Type'} : (term759 _86360) = (term760 _86360).
Proof. exact (MK_COMB (@lem3295152) (@lem3295151 _86360)). Qed.
Lemma lem3295154 {_86360 : Type'} (q : _86360 -> Prop) : (term751 _86360 q) = (term741 _86360 q).
Proof. exact (eq_refl (term751 _86360 q)). Qed.
Lemma lem3295155 {_86360 : Type'} : (term761 _86360) = (term748 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295154 _86360 q)). Qed.
Lemma lem3295156 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295157 {_86360 : Type'} : (term762 _86360) = (term763 _86360).
Proof. exact (MK_COMB (@lem3295156 _86360) (@lem3295155 _86360)). Qed.
Lemma lem3295158 {_86360 : Type'} : (term746 _86360) = (term764 _86360).
Proof. exact (MK_COMB (@lem3295153 _86360) (@lem3295157 _86360)). Qed.
Lemma lem3295159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295160 {_86360 : Type'} : (term790 _86360) = (term791 _86360).
Proof. exact (MK_COMB (@lem3295159) (@lem3295158 _86360)). Qed.
Lemma lem3295161 {_86360 : Type'} (q : _86360 -> Prop) : (term749 _86360 q) = (term736 _86360 q).
Proof. exact (eq_refl (term749 _86360 q)). Qed.
Lemma lem3295162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295163 {_86360 : Type'} (q : _86360 -> Prop) : (term750 _86360 q) = (term738 _86360 q).
Proof. exact (MK_COMB (@lem3295162) (@lem3295161 _86360 q)). Qed.
Lemma lem3295164 {_86360 : Type'} (q : _86360 -> Prop) : (term751 _86360 q) = (term741 _86360 q).
Proof. exact (eq_refl (term751 _86360 q)). Qed.
Lemma lem3295165 {_86360 : Type'} (q : _86360 -> Prop) : (term752 _86360 q) = (term742 _86360 q).
Proof. exact (MK_COMB (@lem3295163 _86360 q) (@lem3295164 _86360 q)). Qed.
Lemma lem3295166 {_86360 : Type'} : (term753 _86360) = (term743 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295165 _86360 q)). Qed.
Lemma lem3295167 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295168 {_86360 : Type'} : (term745 _86360) = (term744 _86360).
Proof. exact (MK_COMB (@lem3295167 _86360) (@lem3295166 _86360)). Qed.
Lemma lem3295169 {_86360 : Type'} : ((term746 _86360) = (term745 _86360)) = ((term764 _86360) = (term744 _86360)).
Proof. exact (MK_COMB (@lem3295160 _86360) (@lem3295168 _86360)). Qed.
Lemma lem3295170 {_86360 : Type'} : (term764 _86360) = (term744 _86360).
Proof. exact (EQ_MP (@lem3295169 _86360) (@lem3295147 _86360)). Qed.
Lemma lem3295172 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295173 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295172 (_86360 -> Prop) P Q). Qed.
Lemma lem3295174 {_86360 : Type'} (q : _86360 -> Prop) : (term724 _86360 q) = (term723 _86360 q).
Proof. exact (@lem3295173 _86360 (term725 _86360 q) (term726 _86360 q)). Qed.
Lemma lem3295175 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term727 _86360 q p) = (term714 _86360 p q).
Proof. exact (eq_refl (term727 _86360 q p)). Qed.
Lemma lem3295176 {_86360 : Type'} (q : _86360 -> Prop) : (term734 _86360 q) = (term725 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295175 _86360 p q)). Qed.
Lemma lem3295177 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295178 {_86360 : Type'} (q : _86360 -> Prop) : (term735 _86360 q) = (term736 _86360 q).
Proof. exact (MK_COMB (@lem3295177 _86360) (@lem3295176 _86360 q)). Qed.
Lemma lem3295179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295180 {_86360 : Type'} (q : _86360 -> Prop) : (term737 _86360 q) = (term738 _86360 q).
Proof. exact (MK_COMB (@lem3295179) (@lem3295178 _86360 q)). Qed.
Lemma lem3295181 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term729 _86360 q p) = (term719 _86360 p q).
Proof. exact (eq_refl (term729 _86360 q p)). Qed.
Lemma lem3295182 {_86360 : Type'} (q : _86360 -> Prop) : (term739 _86360 q) = (term726 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295181 _86360 p q)). Qed.
Lemma lem3295183 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295184 {_86360 : Type'} (q : _86360 -> Prop) : (term740 _86360 q) = (term741 _86360 q).
Proof. exact (MK_COMB (@lem3295183 _86360) (@lem3295182 _86360 q)). Qed.
Lemma lem3295185 {_86360 : Type'} (q : _86360 -> Prop) : (term724 _86360 q) = (term742 _86360 q).
Proof. exact (MK_COMB (@lem3295180 _86360 q) (@lem3295184 _86360 q)). Qed.
Lemma lem3295186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295187 {_86360 : Type'} (q : _86360 -> Prop) : (term792 _86360 q) = (term793 _86360 q).
Proof. exact (MK_COMB (@lem3295186) (@lem3295185 _86360 q)). Qed.
Lemma lem3295188 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term727 _86360 q p) = (term714 _86360 p q).
Proof. exact (eq_refl (term727 _86360 q p)). Qed.
Lemma lem3295189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295190 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term728 _86360 q p) = (term716 _86360 p q).
Proof. exact (MK_COMB (@lem3295189) (@lem3295188 _86360 p q)). Qed.
Lemma lem3295191 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term729 _86360 q p) = (term719 _86360 p q).
Proof. exact (eq_refl (term729 _86360 q p)). Qed.
Lemma lem3295192 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term730 _86360 q p) = (term720 _86360 p q).
Proof. exact (MK_COMB (@lem3295190 _86360 p q) (@lem3295191 _86360 p q)). Qed.
Lemma lem3295193 {_86360 : Type'} (q : _86360 -> Prop) : (term731 _86360 q) = (term721 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295192 _86360 p q)). Qed.
Lemma lem3295194 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295195 {_86360 : Type'} (q : _86360 -> Prop) : (term723 _86360 q) = (term722 _86360 q).
Proof. exact (MK_COMB (@lem3295194 _86360) (@lem3295193 _86360 q)). Qed.
Lemma lem3295196 {_86360 : Type'} (q : _86360 -> Prop) : ((term724 _86360 q) = (term723 _86360 q)) = ((term742 _86360 q) = (term722 _86360 q)).
Proof. exact (MK_COMB (@lem3295187 _86360 q) (@lem3295195 _86360 q)). Qed.
Lemma lem3295197 {_86360 : Type'} (q : _86360 -> Prop) : (term742 _86360 q) = (term722 _86360 q).
Proof. exact (EQ_MP (@lem3295196 _86360 q) (@lem3295174 _86360 q)). Qed.
Lemma lem3295199 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295200 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term459 _86360 P Q) = (term458 _86360 P Q).
Proof. exact (@lem3295199 _86360 P Q). Qed.
Lemma lem3295201 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term702 _86360 p q) = (term701 _86360 p q).
Proof. exact (@lem3295200 _86360 (term703 _86360 p q) (term704 _86360 p q)). Qed.
Lemma lem3295202 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term705 _86360 p q x) = (term419 _86360 p q x).
Proof. exact (eq_refl (term705 _86360 p q x)). Qed.
Lemma lem3295203 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term712 _86360 p q) = (term703 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295202 _86360 p q x)). Qed.
Lemma lem3295204 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295205 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term713 _86360 p q) = (term714 _86360 p q).
Proof. exact (MK_COMB (@lem3295204 _86360) (@lem3295203 _86360 p q)). Qed.
Lemma lem3295206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295207 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term715 _86360 p q) = (term716 _86360 p q).
Proof. exact (MK_COMB (@lem3295206) (@lem3295205 _86360 p q)). Qed.
Lemma lem3295208 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term707 _86360 p q x) = (term416 _86360 p q x).
Proof. exact (eq_refl (term707 _86360 p q x)). Qed.
Lemma lem3295209 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term717 _86360 p q) = (term704 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295208 _86360 p q x)). Qed.
Lemma lem3295210 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295211 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term718 _86360 p q) = (term719 _86360 p q).
Proof. exact (MK_COMB (@lem3295210 _86360) (@lem3295209 _86360 p q)). Qed.
Lemma lem3295212 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term702 _86360 p q) = (term720 _86360 p q).
Proof. exact (MK_COMB (@lem3295207 _86360 p q) (@lem3295211 _86360 p q)). Qed.
Lemma lem3295213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295214 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term794 _86360 p q) = (term795 _86360 p q).
Proof. exact (MK_COMB (@lem3295213) (@lem3295212 _86360 p q)). Qed.
Lemma lem3295215 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term705 _86360 p q x) = (term419 _86360 p q x).
Proof. exact (eq_refl (term705 _86360 p q x)). Qed.
Lemma lem3295216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295217 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term706 _86360 p q x) = (term421 _86360 p q x).
Proof. exact (MK_COMB (@lem3295216) (@lem3295215 _86360 p q x)). Qed.
Lemma lem3295218 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term707 _86360 p q x) = (term416 _86360 p q x).
Proof. exact (eq_refl (term707 _86360 p q x)). Qed.
Lemma lem3295219 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term708 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (MK_COMB (@lem3295217 _86360 p q x) (@lem3295218 _86360 p q x)). Qed.
Lemma lem3295220 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term709 _86360 p q) = (term430 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295219 _86360 p q x)). Qed.
Lemma lem3295221 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295222 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term701 _86360 p q) = (term431 _86360 p q).
Proof. exact (MK_COMB (@lem3295221 _86360) (@lem3295220 _86360 p q)). Qed.
Lemma lem3295223 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term702 _86360 p q) = (term701 _86360 p q)) = ((term720 _86360 p q) = (term431 _86360 p q)).
Proof. exact (MK_COMB (@lem3295214 _86360 p q) (@lem3295222 _86360 p q)). Qed.
Lemma lem3295224 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term720 _86360 p q) = (term431 _86360 p q).
Proof. exact (EQ_MP (@lem3295223 _86360 p q) (@lem3295201 _86360 p q)). Qed.
Lemma lem3295225 {_86360 : Type'} (q : _86360 -> Prop) : (term721 _86360 q) = (term436 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295224 _86360 p q)). Qed.
Lemma lem3295226 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295227 {_86360 : Type'} (q : _86360 -> Prop) : (term722 _86360 q) = (term437 _86360 q).
Proof. exact (MK_COMB (@lem3295226 _86360) (@lem3295225 _86360 q)). Qed.
Lemma lem3295228 {_86360 : Type'} (q : _86360 -> Prop) : (term742 _86360 q) = (term437 _86360 q).
Proof. exact (TRANS (@lem3295197 _86360 q) (@lem3295227 _86360 q)). Qed.
Lemma lem3295229 {_86360 : Type'} : (term743 _86360) = (term442 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295228 _86360 q)). Qed.
Lemma lem3295230 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295231 {_86360 : Type'} : (term744 _86360) = (term443 _86360).
Proof. exact (MK_COMB (@lem3295230 _86360) (@lem3295229 _86360)). Qed.
Lemma lem3295232 {_86360 : Type'} : (term764 _86360) = (term443 _86360).
Proof. exact (TRANS (@lem3295170 _86360) (@lem3295231 _86360)). Qed.
Lemma lem3295233 {_86360 : Type'} : (term765 _86360) = (term447 _86360).
Proof. exact (MK_COMB (@lem3295143 _86360) (@lem3295232 _86360)). Qed.
Lemma lem3295235 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295236 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295235 (_86360 -> Prop) P Q). Qed.
Lemma lem3295237 {_86360 : Type'} : (term796 _86360) = (term797 _86360).
Proof. exact (@lem3295236 _86360 (term408 _86360) (term442 _86360)). Qed.
Lemma lem3295238 {_86360 : Type'} (q : _86360 -> Prop) : (term798 _86360 q) = (term403 _86360 q).
Proof. exact (eq_refl (term798 _86360 q)). Qed.
Lemma lem3295239 {_86360 : Type'} : (term799 _86360) = (term408 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295238 _86360 q)). Qed.
Lemma lem3295240 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295241 {_86360 : Type'} : (term800 _86360) = (term409 _86360).
Proof. exact (MK_COMB (@lem3295240 _86360) (@lem3295239 _86360)). Qed.
Lemma lem3295242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295243 {_86360 : Type'} : (term801 _86360) = (term445 _86360).
Proof. exact (MK_COMB (@lem3295242) (@lem3295241 _86360)). Qed.
Lemma lem3295244 {_86360 : Type'} (q : _86360 -> Prop) : (term802 _86360 q) = (term437 _86360 q).
Proof. exact (eq_refl (term802 _86360 q)). Qed.
Lemma lem3295245 {_86360 : Type'} : (term803 _86360) = (term442 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295244 _86360 q)). Qed.
Lemma lem3295246 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295247 {_86360 : Type'} : (term804 _86360) = (term443 _86360).
Proof. exact (MK_COMB (@lem3295246 _86360) (@lem3295245 _86360)). Qed.
Lemma lem3295248 {_86360 : Type'} : (term796 _86360) = (term447 _86360).
Proof. exact (MK_COMB (@lem3295243 _86360) (@lem3295247 _86360)). Qed.
Lemma lem3295249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295250 {_86360 : Type'} : (term805 _86360) = (term806 _86360).
Proof. exact (MK_COMB (@lem3295249) (@lem3295248 _86360)). Qed.
Lemma lem3295251 {_86360 : Type'} (q : _86360 -> Prop) : (term798 _86360 q) = (term403 _86360 q).
Proof. exact (eq_refl (term798 _86360 q)). Qed.
Lemma lem3295252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295253 {_86360 : Type'} (q : _86360 -> Prop) : (term807 _86360 q) = (term808 _86360 q).
Proof. exact (MK_COMB (@lem3295252) (@lem3295251 _86360 q)). Qed.
Lemma lem3295254 {_86360 : Type'} (q : _86360 -> Prop) : (term802 _86360 q) = (term437 _86360 q).
Proof. exact (eq_refl (term802 _86360 q)). Qed.
Lemma lem3295255 {_86360 : Type'} (q : _86360 -> Prop) : (term809 _86360 q) = (term810 _86360 q).
Proof. exact (MK_COMB (@lem3295253 _86360 q) (@lem3295254 _86360 q)). Qed.
Lemma lem3295256 {_86360 : Type'} : (term811 _86360) = (term812 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295255 _86360 q)). Qed.
Lemma lem3295257 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295258 {_86360 : Type'} : (term797 _86360) = (term813 _86360).
Proof. exact (MK_COMB (@lem3295257 _86360) (@lem3295256 _86360)). Qed.
Lemma lem3295259 {_86360 : Type'} : ((term796 _86360) = (term797 _86360)) = ((term447 _86360) = (term813 _86360)).
Proof. exact (MK_COMB (@lem3295250 _86360) (@lem3295258 _86360)). Qed.
Lemma lem3295260 {_86360 : Type'} : (term447 _86360) = (term813 _86360).
Proof. exact (EQ_MP (@lem3295259 _86360) (@lem3295237 _86360)). Qed.
Lemma lem3295262 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295263 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295262 (_86360 -> Prop) P Q). Qed.
Lemma lem3295264 {_86360 : Type'} (q : _86360 -> Prop) : (term814 _86360 q) = (term815 _86360 q).
Proof. exact (@lem3295263 _86360 (term402 _86360 q) (term436 _86360 q)). Qed.
Lemma lem3295265 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term816 _86360 q p) = (term397 _86360 q p).
Proof. exact (eq_refl (term816 _86360 q p)). Qed.
Lemma lem3295266 {_86360 : Type'} (q : _86360 -> Prop) : (term817 _86360 q) = (term402 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295265 _86360 q p)). Qed.
Lemma lem3295267 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295268 {_86360 : Type'} (q : _86360 -> Prop) : (term818 _86360 q) = (term403 _86360 q).
Proof. exact (MK_COMB (@lem3295267 _86360) (@lem3295266 _86360 q)). Qed.
Lemma lem3295269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295270 {_86360 : Type'} (q : _86360 -> Prop) : (term819 _86360 q) = (term808 _86360 q).
Proof. exact (MK_COMB (@lem3295269) (@lem3295268 _86360 q)). Qed.
Lemma lem3295271 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term820 _86360 q p) = (term431 _86360 p q).
Proof. exact (eq_refl (term820 _86360 q p)). Qed.
Lemma lem3295272 {_86360 : Type'} (q : _86360 -> Prop) : (term821 _86360 q) = (term436 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295271 _86360 p q)). Qed.
Lemma lem3295273 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295274 {_86360 : Type'} (q : _86360 -> Prop) : (term822 _86360 q) = (term437 _86360 q).
Proof. exact (MK_COMB (@lem3295273 _86360) (@lem3295272 _86360 q)). Qed.
Lemma lem3295275 {_86360 : Type'} (q : _86360 -> Prop) : (term814 _86360 q) = (term810 _86360 q).
Proof. exact (MK_COMB (@lem3295270 _86360 q) (@lem3295274 _86360 q)). Qed.
Lemma lem3295276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295277 {_86360 : Type'} (q : _86360 -> Prop) : (term823 _86360 q) = (term824 _86360 q).
Proof. exact (MK_COMB (@lem3295276) (@lem3295275 _86360 q)). Qed.
Lemma lem3295278 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term816 _86360 q p) = (term397 _86360 q p).
Proof. exact (eq_refl (term816 _86360 q p)). Qed.
Lemma lem3295279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295280 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term825 _86360 q p) = (term826 _86360 q p).
Proof. exact (MK_COMB (@lem3295279) (@lem3295278 _86360 q p)). Qed.
Lemma lem3295281 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term820 _86360 q p) = (term431 _86360 p q).
Proof. exact (eq_refl (term820 _86360 q p)). Qed.
Lemma lem3295282 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term827 _86360 q p) = (term828 _86360 p q).
Proof. exact (MK_COMB (@lem3295280 _86360 q p) (@lem3295281 _86360 p q)). Qed.
Lemma lem3295283 {_86360 : Type'} (q : _86360 -> Prop) : (term829 _86360 q) = (term830 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295282 _86360 p q)). Qed.
Lemma lem3295284 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295285 {_86360 : Type'} (q : _86360 -> Prop) : (term815 _86360 q) = (term831 _86360 q).
Proof. exact (MK_COMB (@lem3295284 _86360) (@lem3295283 _86360 q)). Qed.
Lemma lem3295286 {_86360 : Type'} (q : _86360 -> Prop) : ((term814 _86360 q) = (term815 _86360 q)) = ((term810 _86360 q) = (term831 _86360 q)).
Proof. exact (MK_COMB (@lem3295277 _86360 q) (@lem3295285 _86360 q)). Qed.
Lemma lem3295287 {_86360 : Type'} (q : _86360 -> Prop) : (term810 _86360 q) = (term831 _86360 q).
Proof. exact (EQ_MP (@lem3295286 _86360 q) (@lem3295264 _86360 q)). Qed.
Lemma lem3295291 {A : Type'} (P : A -> Prop) (Q : Prop) : (term832 A P Q) = (term833 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3295292 {_86360 : Type'} (P : type686 _86360) (Q : Prop) : (term834 _86360 P Q) = (term835 _86360 P Q).
Proof. exact (@lem3295291 (_86360 -> Prop) P Q). Qed.
Lemma lem3295293 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term836 _86360 p q) = (term837 _86360 p q).
Proof. exact (@lem3295292 _86360 (term396 _86360 q p) (term431 _86360 p q)). Qed.
Lemma lem3295294 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term838 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (eq_refl (term838 _86360 q p r)). Qed.
Lemma lem3295295 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term839 _86360 q p) = (term396 _86360 q p).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295294 _86360 q p r)). Qed.
Lemma lem3295296 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295297 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term840 _86360 q p) = (term397 _86360 q p).
Proof. exact (MK_COMB (@lem3295296 _86360) (@lem3295295 _86360 q p)). Qed.
Lemma lem3295298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295299 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term841 _86360 q p) = (term826 _86360 q p).
Proof. exact (MK_COMB (@lem3295298) (@lem3295297 _86360 q p)). Qed.
Lemma lem3295300 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term431 _86360 p q) = (term431 _86360 p q).
Proof. exact (eq_refl (term431 _86360 p q)). Qed.
Lemma lem3295301 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term836 _86360 p q) = (term828 _86360 p q).
Proof. exact (MK_COMB (@lem3295299 _86360 q p) (@lem3295300 _86360 p q)). Qed.
Lemma lem3295302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295303 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term842 _86360 p q) = (term843 _86360 p q).
Proof. exact (MK_COMB (@lem3295302) (@lem3295301 _86360 p q)). Qed.
Lemma lem3295304 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term838 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (eq_refl (term838 _86360 q p r)). Qed.
Lemma lem3295305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295306 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term844 _86360 q p r) = (term845 _86360 q p r).
Proof. exact (MK_COMB (@lem3295305) (@lem3295304 _86360 q p r)). Qed.
Lemma lem3295307 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term431 _86360 p q) = (term431 _86360 p q).
Proof. exact (eq_refl (term431 _86360 p q)). Qed.
Lemma lem3295308 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term846 _86360 r p q) = (term847 _86360 r p q).
Proof. exact (MK_COMB (@lem3295306 _86360 q p r) (@lem3295307 _86360 p q)). Qed.
Lemma lem3295309 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term848 _86360 p q) = (term849 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295308 _86360 r p q)). Qed.
Lemma lem3295310 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295311 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term837 _86360 p q) = (term850 _86360 p q).
Proof. exact (MK_COMB (@lem3295310 _86360) (@lem3295309 _86360 p q)). Qed.
Lemma lem3295312 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term836 _86360 p q) = (term837 _86360 p q)) = ((term828 _86360 p q) = (term850 _86360 p q)).
Proof. exact (MK_COMB (@lem3295303 _86360 p q) (@lem3295311 _86360 p q)). Qed.
Lemma lem3295313 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term828 _86360 p q) = (term850 _86360 p q).
Proof. exact (EQ_MP (@lem3295312 _86360 p q) (@lem3295293 _86360 p q)). Qed.
Lemma lem3295315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295316 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term459 _86360 P Q) = (term458 _86360 P Q).
Proof. exact (@lem3295315 _86360 P Q). Qed.
Lemma lem3295317 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term851 _86360 r p q) = (term852 _86360 r p q).
Proof. exact (@lem3295316 _86360 (term390 _86360 q p r) (term430 _86360 p q)). Qed.
Lemma lem3295318 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term853 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (eq_refl (term853 _86360 q p r x)). Qed.
Lemma lem3295319 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term854 _86360 q p r) = (term390 _86360 q p r).
Proof. exact (fun_ext (fun x : _86360 => @lem3295318 _86360 q p r x)). Qed.
Lemma lem3295320 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295321 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term855 _86360 q p r) = (term391 _86360 q p r).
Proof. exact (MK_COMB (@lem3295320 _86360) (@lem3295319 _86360 q p r)). Qed.
Lemma lem3295322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295323 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) : (term856 _86360 q p r) = (term845 _86360 q p r).
Proof. exact (MK_COMB (@lem3295322) (@lem3295321 _86360 q p r)). Qed.
Lemma lem3295324 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term857 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (eq_refl (term857 _86360 p q x)). Qed.
Lemma lem3295325 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term858 _86360 p q) = (term430 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295324 _86360 p q x)). Qed.
Lemma lem3295326 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295327 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term859 _86360 p q) = (term431 _86360 p q).
Proof. exact (MK_COMB (@lem3295326 _86360) (@lem3295325 _86360 p q)). Qed.
Lemma lem3295328 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term851 _86360 r p q) = (term847 _86360 r p q).
Proof. exact (MK_COMB (@lem3295323 _86360 q p r) (@lem3295327 _86360 p q)). Qed.
Lemma lem3295329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295330 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term860 _86360 r p q) = (term861 _86360 r p q).
Proof. exact (MK_COMB (@lem3295329) (@lem3295328 _86360 r p q)). Qed.
Lemma lem3295331 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term853 _86360 q p r x) = (term383 _86360 q p r x).
Proof. exact (eq_refl (term853 _86360 q p r x)). Qed.
Lemma lem3295332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295333 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term862 _86360 q p r x) = (term863 _86360 q p r x).
Proof. exact (MK_COMB (@lem3295332) (@lem3295331 _86360 q p r x)). Qed.
Lemma lem3295334 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term857 _86360 p q x) = (term423 _86360 p q x).
Proof. exact (eq_refl (term857 _86360 p q x)). Qed.
Lemma lem3295335 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term864 _86360 r p q x) = (term865 _86360 r p q x).
Proof. exact (MK_COMB (@lem3295333 _86360 q p r x) (@lem3295334 _86360 p q x)). Qed.
Lemma lem3295336 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term866 _86360 r p q) = (term867 _86360 r p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295335 _86360 r p q x)). Qed.
Lemma lem3295337 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295338 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term852 _86360 r p q) = (term868 _86360 r p q).
Proof. exact (MK_COMB (@lem3295337 _86360) (@lem3295336 _86360 r p q)). Qed.
Lemma lem3295339 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term851 _86360 r p q) = (term852 _86360 r p q)) = ((term847 _86360 r p q) = (term868 _86360 r p q)).
Proof. exact (MK_COMB (@lem3295330 _86360 r p q) (@lem3295338 _86360 r p q)). Qed.
Lemma lem3295340 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term847 _86360 r p q) = (term868 _86360 r p q).
Proof. exact (EQ_MP (@lem3295339 _86360 r p q) (@lem3295317 _86360 r p q)). Qed.
Lemma lem3295341 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term849 _86360 p q) = (term869 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295340 _86360 r p q)). Qed.
Lemma lem3295342 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295343 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term850 _86360 p q) = (term870 _86360 p q).
Proof. exact (MK_COMB (@lem3295342 _86360) (@lem3295341 _86360 p q)). Qed.
Lemma lem3295344 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term828 _86360 p q) = (term870 _86360 p q).
Proof. exact (TRANS (@lem3295313 _86360 p q) (@lem3295343 _86360 p q)). Qed.
Lemma lem3295345 {_86360 : Type'} (q : _86360 -> Prop) : (term830 _86360 q) = (term871 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295344 _86360 p q)). Qed.
Lemma lem3295346 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295347 {_86360 : Type'} (q : _86360 -> Prop) : (term831 _86360 q) = (term872 _86360 q).
Proof. exact (MK_COMB (@lem3295346 _86360) (@lem3295345 _86360 q)). Qed.
Lemma lem3295348 {_86360 : Type'} (q : _86360 -> Prop) : (term810 _86360 q) = (term872 _86360 q).
Proof. exact (TRANS (@lem3295287 _86360 q) (@lem3295347 _86360 q)). Qed.
Lemma lem3295349 {_86360 : Type'} : (term812 _86360) = (term873 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295348 _86360 q)). Qed.
Lemma lem3295350 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295351 {_86360 : Type'} : (term813 _86360) = (term874 _86360).
Proof. exact (MK_COMB (@lem3295350 _86360) (@lem3295349 _86360)). Qed.
Lemma lem3295352 {_86360 : Type'} : (term447 _86360) = (term874 _86360).
Proof. exact (TRANS (@lem3295260 _86360) (@lem3295351 _86360)). Qed.
Lemma lem3295353 {_86360 : Type'} : (term765 _86360) = (term874 _86360).
Proof. exact (TRANS (@lem3295233 _86360) (@lem3295352 _86360)). Qed.
Lemma lem3295354 {_86360 : Type'} : (term766 _86360) = (term875 _86360).
Proof. exact (MK_COMB (@lem3295021 _86360) (@lem3295353 _86360)). Qed.
Lemma lem3295356 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295357 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295356 (_86360 -> Prop) P Q). Qed.
Lemma lem3295358 {_86360 : Type'} : (term876 _86360) = (term877 _86360).
Proof. exact (@lem3295357 _86360 (term371 _86360) (term873 _86360)). Qed.
Lemma lem3295359 {_86360 : Type'} (q : _86360 -> Prop) : (term878 _86360 q) = (term366 _86360 q).
Proof. exact (eq_refl (term878 _86360 q)). Qed.
Lemma lem3295360 {_86360 : Type'} : (term879 _86360) = (term371 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295359 _86360 q)). Qed.
Lemma lem3295361 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295362 {_86360 : Type'} : (term880 _86360) = (term372 _86360).
Proof. exact (MK_COMB (@lem3295361 _86360) (@lem3295360 _86360)). Qed.
Lemma lem3295363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295364 {_86360 : Type'} : (term881 _86360) = (term450 _86360).
Proof. exact (MK_COMB (@lem3295363) (@lem3295362 _86360)). Qed.
Lemma lem3295365 {_86360 : Type'} (q : _86360 -> Prop) : (term882 _86360 q) = (term872 _86360 q).
Proof. exact (eq_refl (term882 _86360 q)). Qed.
Lemma lem3295366 {_86360 : Type'} : (term883 _86360) = (term873 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295365 _86360 q)). Qed.
Lemma lem3295367 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295368 {_86360 : Type'} : (term884 _86360) = (term874 _86360).
Proof. exact (MK_COMB (@lem3295367 _86360) (@lem3295366 _86360)). Qed.
Lemma lem3295369 {_86360 : Type'} : (term876 _86360) = (term875 _86360).
Proof. exact (MK_COMB (@lem3295364 _86360) (@lem3295368 _86360)). Qed.
Lemma lem3295370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295371 {_86360 : Type'} : (term885 _86360) = (term886 _86360).
Proof. exact (MK_COMB (@lem3295370) (@lem3295369 _86360)). Qed.
Lemma lem3295372 {_86360 : Type'} (q : _86360 -> Prop) : (term878 _86360 q) = (term366 _86360 q).
Proof. exact (eq_refl (term878 _86360 q)). Qed.
Lemma lem3295373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295374 {_86360 : Type'} (q : _86360 -> Prop) : (term887 _86360 q) = (term888 _86360 q).
Proof. exact (MK_COMB (@lem3295373) (@lem3295372 _86360 q)). Qed.
Lemma lem3295375 {_86360 : Type'} (q : _86360 -> Prop) : (term882 _86360 q) = (term872 _86360 q).
Proof. exact (eq_refl (term882 _86360 q)). Qed.
Lemma lem3295376 {_86360 : Type'} (q : _86360 -> Prop) : (term889 _86360 q) = (term890 _86360 q).
Proof. exact (MK_COMB (@lem3295374 _86360 q) (@lem3295375 _86360 q)). Qed.
Lemma lem3295377 {_86360 : Type'} : (term891 _86360) = (term892 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295376 _86360 q)). Qed.
Lemma lem3295378 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295379 {_86360 : Type'} : (term877 _86360) = (term893 _86360).
Proof. exact (MK_COMB (@lem3295378 _86360) (@lem3295377 _86360)). Qed.
Lemma lem3295380 {_86360 : Type'} : ((term876 _86360) = (term877 _86360)) = ((term875 _86360) = (term893 _86360)).
Proof. exact (MK_COMB (@lem3295371 _86360) (@lem3295379 _86360)). Qed.
Lemma lem3295381 {_86360 : Type'} : (term875 _86360) = (term893 _86360).
Proof. exact (EQ_MP (@lem3295380 _86360) (@lem3295358 _86360)). Qed.
Lemma lem3295383 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295384 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295383 (_86360 -> Prop) P Q). Qed.
Lemma lem3295385 {_86360 : Type'} (q : _86360 -> Prop) : (term894 _86360 q) = (term895 _86360 q).
Proof. exact (@lem3295384 _86360 (term365 _86360 q) (term871 _86360 q)). Qed.
Lemma lem3295386 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term896 _86360 q p) = (term360 _86360 p q).
Proof. exact (eq_refl (term896 _86360 q p)). Qed.
Lemma lem3295387 {_86360 : Type'} (q : _86360 -> Prop) : (term897 _86360 q) = (term365 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295386 _86360 p q)). Qed.
Lemma lem3295388 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295389 {_86360 : Type'} (q : _86360 -> Prop) : (term898 _86360 q) = (term366 _86360 q).
Proof. exact (MK_COMB (@lem3295388 _86360) (@lem3295387 _86360 q)). Qed.
Lemma lem3295390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295391 {_86360 : Type'} (q : _86360 -> Prop) : (term899 _86360 q) = (term888 _86360 q).
Proof. exact (MK_COMB (@lem3295390) (@lem3295389 _86360 q)). Qed.
Lemma lem3295392 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term900 _86360 q p) = (term870 _86360 p q).
Proof. exact (eq_refl (term900 _86360 q p)). Qed.
Lemma lem3295393 {_86360 : Type'} (q : _86360 -> Prop) : (term901 _86360 q) = (term871 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295392 _86360 p q)). Qed.
Lemma lem3295394 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295395 {_86360 : Type'} (q : _86360 -> Prop) : (term902 _86360 q) = (term872 _86360 q).
Proof. exact (MK_COMB (@lem3295394 _86360) (@lem3295393 _86360 q)). Qed.
Lemma lem3295396 {_86360 : Type'} (q : _86360 -> Prop) : (term894 _86360 q) = (term890 _86360 q).
Proof. exact (MK_COMB (@lem3295391 _86360 q) (@lem3295395 _86360 q)). Qed.
Lemma lem3295397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295398 {_86360 : Type'} (q : _86360 -> Prop) : (term903 _86360 q) = (term904 _86360 q).
Proof. exact (MK_COMB (@lem3295397) (@lem3295396 _86360 q)). Qed.
Lemma lem3295399 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term896 _86360 q p) = (term360 _86360 p q).
Proof. exact (eq_refl (term896 _86360 q p)). Qed.
Lemma lem3295400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295401 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term905 _86360 q p) = (term906 _86360 p q).
Proof. exact (MK_COMB (@lem3295400) (@lem3295399 _86360 p q)). Qed.
Lemma lem3295402 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term900 _86360 q p) = (term870 _86360 p q).
Proof. exact (eq_refl (term900 _86360 q p)). Qed.
Lemma lem3295403 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term907 _86360 q p) = (term908 _86360 p q).
Proof. exact (MK_COMB (@lem3295401 _86360 p q) (@lem3295402 _86360 p q)). Qed.
Lemma lem3295404 {_86360 : Type'} (q : _86360 -> Prop) : (term909 _86360 q) = (term910 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295403 _86360 p q)). Qed.
Lemma lem3295405 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295406 {_86360 : Type'} (q : _86360 -> Prop) : (term895 _86360 q) = (term911 _86360 q).
Proof. exact (MK_COMB (@lem3295405 _86360) (@lem3295404 _86360 q)). Qed.
Lemma lem3295407 {_86360 : Type'} (q : _86360 -> Prop) : ((term894 _86360 q) = (term895 _86360 q)) = ((term890 _86360 q) = (term911 _86360 q)).
Proof. exact (MK_COMB (@lem3295398 _86360 q) (@lem3295406 _86360 q)). Qed.
Lemma lem3295408 {_86360 : Type'} (q : _86360 -> Prop) : (term890 _86360 q) = (term911 _86360 q).
Proof. exact (EQ_MP (@lem3295407 _86360 q) (@lem3295385 _86360 q)). Qed.
Lemma lem3295410 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295411 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295410 (_86360 -> Prop) P Q). Qed.
Lemma lem3295412 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term912 _86360 p q) = (term913 _86360 p q).
Proof. exact (@lem3295411 _86360 (term359 _86360 p q) (term869 _86360 p q)). Qed.
Lemma lem3295413 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term914 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (eq_refl (term914 _86360 p q r)). Qed.
Lemma lem3295414 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term915 _86360 p q) = (term359 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295413 _86360 p q r)). Qed.
Lemma lem3295415 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295416 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term916 _86360 p q) = (term360 _86360 p q).
Proof. exact (MK_COMB (@lem3295415 _86360) (@lem3295414 _86360 p q)). Qed.
Lemma lem3295417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295418 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term917 _86360 p q) = (term906 _86360 p q).
Proof. exact (MK_COMB (@lem3295417) (@lem3295416 _86360 p q)). Qed.
Lemma lem3295419 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term918 _86360 p q r) = (term868 _86360 r p q).
Proof. exact (eq_refl (term918 _86360 p q r)). Qed.
Lemma lem3295420 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term919 _86360 p q) = (term869 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295419 _86360 r p q)). Qed.
Lemma lem3295421 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295422 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term920 _86360 p q) = (term870 _86360 p q).
Proof. exact (MK_COMB (@lem3295421 _86360) (@lem3295420 _86360 p q)). Qed.
Lemma lem3295423 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term912 _86360 p q) = (term908 _86360 p q).
Proof. exact (MK_COMB (@lem3295418 _86360 p q) (@lem3295422 _86360 p q)). Qed.
Lemma lem3295424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295425 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term921 _86360 p q) = (term922 _86360 p q).
Proof. exact (MK_COMB (@lem3295424) (@lem3295423 _86360 p q)). Qed.
Lemma lem3295426 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term914 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (eq_refl (term914 _86360 p q r)). Qed.
Lemma lem3295427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295428 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term923 _86360 p q r) = (term924 _86360 p q r).
Proof. exact (MK_COMB (@lem3295427) (@lem3295426 _86360 p q r)). Qed.
Lemma lem3295429 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term918 _86360 p q r) = (term868 _86360 r p q).
Proof. exact (eq_refl (term918 _86360 p q r)). Qed.
Lemma lem3295430 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term925 _86360 p q r) = (term926 _86360 r p q).
Proof. exact (MK_COMB (@lem3295428 _86360 p q r) (@lem3295429 _86360 r p q)). Qed.
Lemma lem3295431 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term927 _86360 p q) = (term928 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295430 _86360 r p q)). Qed.
Lemma lem3295432 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295433 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term913 _86360 p q) = (term929 _86360 p q).
Proof. exact (MK_COMB (@lem3295432 _86360) (@lem3295431 _86360 p q)). Qed.
Lemma lem3295434 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term912 _86360 p q) = (term913 _86360 p q)) = ((term908 _86360 p q) = (term929 _86360 p q)).
Proof. exact (MK_COMB (@lem3295425 _86360 p q) (@lem3295433 _86360 p q)). Qed.
Lemma lem3295435 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term908 _86360 p q) = (term929 _86360 p q).
Proof. exact (EQ_MP (@lem3295434 _86360 p q) (@lem3295412 _86360 p q)). Qed.
Lemma lem3295437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295438 {_86360 : Type'} (P : _86360 -> Prop) (Q : _86360 -> Prop) : (term459 _86360 P Q) = (term458 _86360 P Q).
Proof. exact (@lem3295437 _86360 P Q). Qed.
Lemma lem3295439 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term930 _86360 r p q) = (term931 _86360 r p q).
Proof. exact (@lem3295438 _86360 (term353 _86360 p q r) (term867 _86360 r p q)). Qed.
Lemma lem3295440 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term932 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (eq_refl (term932 _86360 p q r x)). Qed.
Lemma lem3295441 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term933 _86360 p q r) = (term353 _86360 p q r).
Proof. exact (fun_ext (fun x : _86360 => @lem3295440 _86360 p q r x)). Qed.
Lemma lem3295442 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295443 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term934 _86360 p q r) = (term354 _86360 p q r).
Proof. exact (MK_COMB (@lem3295442 _86360) (@lem3295441 _86360 p q r)). Qed.
Lemma lem3295444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295445 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : (term935 _86360 p q r) = (term924 _86360 p q r).
Proof. exact (MK_COMB (@lem3295444) (@lem3295443 _86360 p q r)). Qed.
Lemma lem3295446 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term936 _86360 r p q x) = (term865 _86360 r p q x).
Proof. exact (eq_refl (term936 _86360 r p q x)). Qed.
Lemma lem3295447 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term937 _86360 r p q) = (term867 _86360 r p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295446 _86360 r p q x)). Qed.
Lemma lem3295448 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295449 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term938 _86360 r p q) = (term868 _86360 r p q).
Proof. exact (MK_COMB (@lem3295448 _86360) (@lem3295447 _86360 r p q)). Qed.
Lemma lem3295450 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term930 _86360 r p q) = (term926 _86360 r p q).
Proof. exact (MK_COMB (@lem3295445 _86360 p q r) (@lem3295449 _86360 r p q)). Qed.
Lemma lem3295451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295452 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term939 _86360 r p q) = (term940 _86360 r p q).
Proof. exact (MK_COMB (@lem3295451) (@lem3295450 _86360 r p q)). Qed.
Lemma lem3295453 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term932 _86360 p q r x) = (term346 _86360 p q r x).
Proof. exact (eq_refl (term932 _86360 p q r x)). Qed.
Lemma lem3295454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295455 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x : _86360) : (term941 _86360 p q r x) = (term942 _86360 p q r x).
Proof. exact (MK_COMB (@lem3295454) (@lem3295453 _86360 p q r x)). Qed.
Lemma lem3295456 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term936 _86360 r p q x) = (term865 _86360 r p q x).
Proof. exact (eq_refl (term936 _86360 r p q x)). Qed.
Lemma lem3295457 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term943 _86360 r p q x) = (term944 _86360 r p q x).
Proof. exact (MK_COMB (@lem3295455 _86360 p q r x) (@lem3295456 _86360 r p q x)). Qed.
Lemma lem3295458 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term945 _86360 r p q) = (term946 _86360 r p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295457 _86360 r p q x)). Qed.
Lemma lem3295459 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295460 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term931 _86360 r p q) = (term947 _86360 r p q).
Proof. exact (MK_COMB (@lem3295459 _86360) (@lem3295458 _86360 r p q)). Qed.
Lemma lem3295461 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term930 _86360 r p q) = (term931 _86360 r p q)) = ((term926 _86360 r p q) = (term947 _86360 r p q)).
Proof. exact (MK_COMB (@lem3295452 _86360 r p q) (@lem3295460 _86360 r p q)). Qed.
Lemma lem3295462 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term926 _86360 r p q) = (term947 _86360 r p q).
Proof. exact (EQ_MP (@lem3295461 _86360 r p q) (@lem3295439 _86360 r p q)). Qed.
Lemma lem3295463 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term928 _86360 p q) = (term948 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295462 _86360 r p q)). Qed.
Lemma lem3295464 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295465 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term929 _86360 p q) = (term949 _86360 p q).
Proof. exact (MK_COMB (@lem3295464 _86360) (@lem3295463 _86360 p q)). Qed.
Lemma lem3295466 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term908 _86360 p q) = (term949 _86360 p q).
Proof. exact (TRANS (@lem3295435 _86360 p q) (@lem3295465 _86360 p q)). Qed.
Lemma lem3295467 {_86360 : Type'} (q : _86360 -> Prop) : (term910 _86360 q) = (term950 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295466 _86360 p q)). Qed.
Lemma lem3295468 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295469 {_86360 : Type'} (q : _86360 -> Prop) : (term911 _86360 q) = (term951 _86360 q).
Proof. exact (MK_COMB (@lem3295468 _86360) (@lem3295467 _86360 q)). Qed.
Lemma lem3295470 {_86360 : Type'} (q : _86360 -> Prop) : (term890 _86360 q) = (term951 _86360 q).
Proof. exact (TRANS (@lem3295408 _86360 q) (@lem3295469 _86360 q)). Qed.
Lemma lem3295471 {_86360 : Type'} : (term892 _86360) = (term952 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295470 _86360 q)). Qed.
Lemma lem3295472 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295473 {_86360 : Type'} : (term893 _86360) = (term953 _86360).
Proof. exact (MK_COMB (@lem3295472 _86360) (@lem3295471 _86360)). Qed.
Lemma lem3295474 {_86360 : Type'} : (term875 _86360) = (term953 _86360).
Proof. exact (TRANS (@lem3295381 _86360) (@lem3295473 _86360)). Qed.
Lemma lem3295475 {_86360 : Type'} : (term766 _86360) = (term953 _86360).
Proof. exact (TRANS (@lem3295354 _86360) (@lem3295474 _86360)). Qed.
Lemma lem3295476 {_86360 : Type'} : (term767 _86360) = (term954 _86360).
Proof. exact (MK_COMB (@lem3294899 _86360) (@lem3295475 _86360)). Qed.
Lemma lem3295478 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295479 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295478 (_86360 -> Prop) P Q). Qed.
Lemma lem3295480 {_86360 : Type'} : (term955 _86360) = (term956 _86360).
Proof. exact (@lem3295479 _86360 (term324 _86360) (term952 _86360)). Qed.
Lemma lem3295481 {_86360 : Type'} (q : _86360 -> Prop) : (term957 _86360 q) = (term319 _86360 q).
Proof. exact (eq_refl (term957 _86360 q)). Qed.
Lemma lem3295482 {_86360 : Type'} : (term958 _86360) = (term324 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295481 _86360 q)). Qed.
Lemma lem3295483 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295484 {_86360 : Type'} : (term959 _86360) = (term325 _86360).
Proof. exact (MK_COMB (@lem3295483 _86360) (@lem3295482 _86360)). Qed.
Lemma lem3295485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295486 {_86360 : Type'} : (term960 _86360) = (term455 _86360).
Proof. exact (MK_COMB (@lem3295485) (@lem3295484 _86360)). Qed.
Lemma lem3295487 {_86360 : Type'} (q : _86360 -> Prop) : (term961 _86360 q) = (term951 _86360 q).
Proof. exact (eq_refl (term961 _86360 q)). Qed.
Lemma lem3295488 {_86360 : Type'} : (term962 _86360) = (term952 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295487 _86360 q)). Qed.
Lemma lem3295489 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295490 {_86360 : Type'} : (term963 _86360) = (term953 _86360).
Proof. exact (MK_COMB (@lem3295489 _86360) (@lem3295488 _86360)). Qed.
Lemma lem3295491 {_86360 : Type'} : (term955 _86360) = (term954 _86360).
Proof. exact (MK_COMB (@lem3295486 _86360) (@lem3295490 _86360)). Qed.
Lemma lem3295492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295493 {_86360 : Type'} : (term964 _86360) = (term965 _86360).
Proof. exact (MK_COMB (@lem3295492) (@lem3295491 _86360)). Qed.
Lemma lem3295494 {_86360 : Type'} (q : _86360 -> Prop) : (term957 _86360 q) = (term319 _86360 q).
Proof. exact (eq_refl (term957 _86360 q)). Qed.
Lemma lem3295495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295496 {_86360 : Type'} (q : _86360 -> Prop) : (term966 _86360 q) = (term967 _86360 q).
Proof. exact (MK_COMB (@lem3295495) (@lem3295494 _86360 q)). Qed.
Lemma lem3295497 {_86360 : Type'} (q : _86360 -> Prop) : (term961 _86360 q) = (term951 _86360 q).
Proof. exact (eq_refl (term961 _86360 q)). Qed.
Lemma lem3295498 {_86360 : Type'} (q : _86360 -> Prop) : (term968 _86360 q) = (term969 _86360 q).
Proof. exact (MK_COMB (@lem3295496 _86360 q) (@lem3295497 _86360 q)). Qed.
Lemma lem3295499 {_86360 : Type'} : (term970 _86360) = (term971 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295498 _86360 q)). Qed.
Lemma lem3295500 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295501 {_86360 : Type'} : (term956 _86360) = (term972 _86360).
Proof. exact (MK_COMB (@lem3295500 _86360) (@lem3295499 _86360)). Qed.
Lemma lem3295502 {_86360 : Type'} : ((term955 _86360) = (term956 _86360)) = ((term954 _86360) = (term972 _86360)).
Proof. exact (MK_COMB (@lem3295493 _86360) (@lem3295501 _86360)). Qed.
Lemma lem3295503 {_86360 : Type'} : (term954 _86360) = (term972 _86360).
Proof. exact (EQ_MP (@lem3295502 _86360) (@lem3295480 _86360)). Qed.
Lemma lem3295505 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term459 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3295506 {_86360 : Type'} (P : type686 _86360) (Q : type686 _86360) : (term483 _86360 P Q) = (term482 _86360 P Q).
Proof. exact (@lem3295505 (_86360 -> Prop) P Q). Qed.
Lemma lem3295507 {_86360 : Type'} (q : _86360 -> Prop) : (term973 _86360 q) = (term974 _86360 q).
Proof. exact (@lem3295506 _86360 (term318 _86360 q) (term950 _86360 q)). Qed.
Lemma lem3295508 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term975 _86360 q p) = (term311 _86360 q p).
Proof. exact (eq_refl (term975 _86360 q p)). Qed.
Lemma lem3295509 {_86360 : Type'} (q : _86360 -> Prop) : (term976 _86360 q) = (term318 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295508 _86360 q p)). Qed.
Lemma lem3295510 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295511 {_86360 : Type'} (q : _86360 -> Prop) : (term977 _86360 q) = (term319 _86360 q).
Proof. exact (MK_COMB (@lem3295510 _86360) (@lem3295509 _86360 q)). Qed.
Lemma lem3295512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295513 {_86360 : Type'} (q : _86360 -> Prop) : (term978 _86360 q) = (term967 _86360 q).
Proof. exact (MK_COMB (@lem3295512) (@lem3295511 _86360 q)). Qed.
Lemma lem3295514 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term979 _86360 q p) = (term949 _86360 p q).
Proof. exact (eq_refl (term979 _86360 q p)). Qed.
Lemma lem3295515 {_86360 : Type'} (q : _86360 -> Prop) : (term980 _86360 q) = (term950 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295514 _86360 p q)). Qed.
Lemma lem3295516 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295517 {_86360 : Type'} (q : _86360 -> Prop) : (term981 _86360 q) = (term951 _86360 q).
Proof. exact (MK_COMB (@lem3295516 _86360) (@lem3295515 _86360 q)). Qed.
Lemma lem3295518 {_86360 : Type'} (q : _86360 -> Prop) : (term973 _86360 q) = (term969 _86360 q).
Proof. exact (MK_COMB (@lem3295513 _86360 q) (@lem3295517 _86360 q)). Qed.
Lemma lem3295519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295520 {_86360 : Type'} (q : _86360 -> Prop) : (term982 _86360 q) = (term983 _86360 q).
Proof. exact (MK_COMB (@lem3295519) (@lem3295518 _86360 q)). Qed.
Lemma lem3295521 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term975 _86360 q p) = (term311 _86360 q p).
Proof. exact (eq_refl (term975 _86360 q p)). Qed.
Lemma lem3295522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295523 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term984 _86360 q p) = (term985 _86360 q p).
Proof. exact (MK_COMB (@lem3295522) (@lem3295521 _86360 q p)). Qed.
Lemma lem3295524 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term979 _86360 q p) = (term949 _86360 p q).
Proof. exact (eq_refl (term979 _86360 q p)). Qed.
Lemma lem3295525 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term986 _86360 q p) = (term987 _86360 p q).
Proof. exact (MK_COMB (@lem3295523 _86360 q p) (@lem3295524 _86360 p q)). Qed.
Lemma lem3295526 {_86360 : Type'} (q : _86360 -> Prop) : (term988 _86360 q) = (term989 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295525 _86360 p q)). Qed.
Lemma lem3295527 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295528 {_86360 : Type'} (q : _86360 -> Prop) : (term974 _86360 q) = (term990 _86360 q).
Proof. exact (MK_COMB (@lem3295527 _86360) (@lem3295526 _86360 q)). Qed.
Lemma lem3295529 {_86360 : Type'} (q : _86360 -> Prop) : ((term973 _86360 q) = (term974 _86360 q)) = ((term969 _86360 q) = (term990 _86360 q)).
Proof. exact (MK_COMB (@lem3295520 _86360 q) (@lem3295528 _86360 q)). Qed.
Lemma lem3295530 {_86360 : Type'} (q : _86360 -> Prop) : (term969 _86360 q) = (term990 _86360 q).
Proof. exact (EQ_MP (@lem3295529 _86360 q) (@lem3295507 _86360 q)). Qed.
Lemma lem3295534 {A : Type'} (P : A -> Prop) (Q : Prop) : (term832 A P Q) = (term833 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3295535 {_86360 : Type'} (P : _86360 -> Prop) (Q : Prop) : (term832 _86360 P Q) = (term833 _86360 P Q).
Proof. exact (@lem3295534 _86360 P Q). Qed.
Lemma lem3295536 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term991 _86360 p q) = (term992 _86360 p q).
Proof. exact (@lem3295535 _86360 (term310 _86360 q p) (term949 _86360 p q)). Qed.
Lemma lem3295537 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term993 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (eq_refl (term993 _86360 q p x)). Qed.
Lemma lem3295538 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term994 _86360 q p) = (term310 _86360 q p).
Proof. exact (fun_ext (fun x : _86360 => @lem3295537 _86360 q p x)). Qed.
Lemma lem3295539 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295540 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term995 _86360 q p) = (term311 _86360 q p).
Proof. exact (MK_COMB (@lem3295539 _86360) (@lem3295538 _86360 q p)). Qed.
Lemma lem3295541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295542 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : (term996 _86360 q p) = (term985 _86360 q p).
Proof. exact (MK_COMB (@lem3295541) (@lem3295540 _86360 q p)). Qed.
Lemma lem3295543 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term949 _86360 p q) = (term949 _86360 p q).
Proof. exact (eq_refl (term949 _86360 p q)). Qed.
Lemma lem3295544 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term991 _86360 p q) = (term987 _86360 p q).
Proof. exact (MK_COMB (@lem3295542 _86360 q p) (@lem3295543 _86360 p q)). Qed.
Lemma lem3295545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295546 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term997 _86360 p q) = (term998 _86360 p q).
Proof. exact (MK_COMB (@lem3295545) (@lem3295544 _86360 p q)). Qed.
Lemma lem3295547 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term993 _86360 q p x) = (term301 _86360 q p x).
Proof. exact (eq_refl (term993 _86360 q p x)). Qed.
Lemma lem3295548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3295549 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term999 _86360 q p x) = (term1000 _86360 q p x).
Proof. exact (MK_COMB (@lem3295548) (@lem3295547 _86360 q p x)). Qed.
Lemma lem3295550 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term949 _86360 p q) = (term949 _86360 p q).
Proof. exact (eq_refl (term949 _86360 p q)). Qed.
Lemma lem3295551 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1001 _86360 x p q) = (term1002 _86360 x p q).
Proof. exact (MK_COMB (@lem3295549 _86360 q p x) (@lem3295550 _86360 p q)). Qed.
Lemma lem3295552 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1003 _86360 p q) = (term1004 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295551 _86360 x p q)). Qed.
Lemma lem3295553 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295554 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term992 _86360 p q) = (term1005 _86360 p q).
Proof. exact (MK_COMB (@lem3295553 _86360) (@lem3295552 _86360 p q)). Qed.
Lemma lem3295555 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term991 _86360 p q) = (term992 _86360 p q)) = ((term987 _86360 p q) = (term1005 _86360 p q)).
Proof. exact (MK_COMB (@lem3295546 _86360 p q) (@lem3295554 _86360 p q)). Qed.
Lemma lem3295556 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term987 _86360 p q) = (term1005 _86360 p q).
Proof. exact (EQ_MP (@lem3295555 _86360 p q) (@lem3295536 _86360 p q)). Qed.
Lemma lem3295558 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1006 A P Q) = (term1007 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3295559 {_86360 : Type'} (P : Prop) (Q : type686 _86360) : (term1008 _86360 P Q) = (term1009 _86360 P Q).
Proof. exact (@lem3295558 (_86360 -> Prop) P Q). Qed.
Lemma lem3295560 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1010 _86360 x p q) = (term1011 _86360 x p q).
Proof. exact (@lem3295559 _86360 (term301 _86360 q p x) (term948 _86360 p q)). Qed.
Lemma lem3295561 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1012 _86360 p q r) = (term947 _86360 r p q).
Proof. exact (eq_refl (term1012 _86360 p q r)). Qed.
Lemma lem3295562 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1013 _86360 p q) = (term948 _86360 p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295561 _86360 r p q)). Qed.
Lemma lem3295563 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295564 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1014 _86360 p q) = (term949 _86360 p q).
Proof. exact (MK_COMB (@lem3295563 _86360) (@lem3295562 _86360 p q)). Qed.
Lemma lem3295565 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term1000 _86360 q p x) = (term1000 _86360 q p x).
Proof. exact (eq_refl (term1000 _86360 q p x)). Qed.
Lemma lem3295566 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1010 _86360 x p q) = (term1002 _86360 x p q).
Proof. exact (MK_COMB (@lem3295565 _86360 q p x) (@lem3295564 _86360 p q)). Qed.
Lemma lem3295567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295568 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1015 _86360 x p q) = (term1016 _86360 x p q).
Proof. exact (MK_COMB (@lem3295567) (@lem3295566 _86360 x p q)). Qed.
Lemma lem3295569 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1012 _86360 p q r) = (term947 _86360 r p q).
Proof. exact (eq_refl (term1012 _86360 p q r)). Qed.
Lemma lem3295570 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term1000 _86360 q p x) = (term1000 _86360 q p x).
Proof. exact (eq_refl (term1000 _86360 q p x)). Qed.
Lemma lem3295571 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1017 _86360 x p q r) = (term1018 _86360 x r p q).
Proof. exact (MK_COMB (@lem3295570 _86360 q p x) (@lem3295569 _86360 r p q)). Qed.
Lemma lem3295572 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1019 _86360 x p q) = (term1020 _86360 x p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295571 _86360 x r p q)). Qed.
Lemma lem3295573 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295574 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1011 _86360 x p q) = (term1021 _86360 x p q).
Proof. exact (MK_COMB (@lem3295573 _86360) (@lem3295572 _86360 x p q)). Qed.
Lemma lem3295575 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term1010 _86360 x p q) = (term1011 _86360 x p q)) = ((term1002 _86360 x p q) = (term1021 _86360 x p q)).
Proof. exact (MK_COMB (@lem3295568 _86360 x p q) (@lem3295574 _86360 x p q)). Qed.
Lemma lem3295576 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1002 _86360 x p q) = (term1021 _86360 x p q).
Proof. exact (EQ_MP (@lem3295575 _86360 x p q) (@lem3295560 _86360 x p q)). Qed.
Lemma lem3295578 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1006 A P Q) = (term1007 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3295579 {_86360 : Type'} (P : Prop) (Q : _86360 -> Prop) : (term1006 _86360 P Q) = (term1007 _86360 P Q).
Proof. exact (@lem3295578 _86360 P Q). Qed.
Lemma lem3295580 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1022 _86360 x r p q) = (term1023 _86360 x r p q).
Proof. exact (@lem3295579 _86360 (term301 _86360 q p x) (term946 _86360 r p q)). Qed.
Lemma lem3295581 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x : _86360) : (term1024 _86360 r p q x) = (term944 _86360 r p q x).
Proof. exact (eq_refl (term1024 _86360 r p q x)). Qed.
Lemma lem3295582 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1025 _86360 r p q) = (term946 _86360 r p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295581 _86360 r p q x)). Qed.
Lemma lem3295583 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295584 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1026 _86360 r p q) = (term947 _86360 r p q).
Proof. exact (MK_COMB (@lem3295583 _86360) (@lem3295582 _86360 r p q)). Qed.
Lemma lem3295585 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term1000 _86360 q p x) = (term1000 _86360 q p x).
Proof. exact (eq_refl (term1000 _86360 q p x)). Qed.
Lemma lem3295586 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1022 _86360 x r p q) = (term1018 _86360 x r p q).
Proof. exact (MK_COMB (@lem3295585 _86360 q p x) (@lem3295584 _86360 r p q)). Qed.
Lemma lem3295587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3295588 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1027 _86360 x r p q) = (term1028 _86360 x r p q).
Proof. exact (MK_COMB (@lem3295587) (@lem3295586 _86360 x r p q)). Qed.
Lemma lem3295589 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) : (term1024 _86360 r p q x') = (term944 _86360 r p q x').
Proof. exact (eq_refl (term1024 _86360 r p q x')). Qed.
Lemma lem3295590 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) : (term1000 _86360 q p x) = (term1000 _86360 q p x).
Proof. exact (eq_refl (term1000 _86360 q p x)). Qed.
Lemma lem3295591 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) : (term1029 _86360 x r p q x') = (term1030 _86360 x r p q x').
Proof. exact (MK_COMB (@lem3295590 _86360 q p x) (@lem3295589 _86360 r p q x')). Qed.
Lemma lem3295592 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1031 _86360 x r p q) = (term1032 _86360 x r p q).
Proof. exact (fun_ext (fun x' : _86360 => @lem3295591 _86360 x r p q x')). Qed.
Lemma lem3295593 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295594 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1023 _86360 x r p q) = (term1033 _86360 x r p q).
Proof. exact (MK_COMB (@lem3295593 _86360) (@lem3295592 _86360 x r p q)). Qed.
Lemma lem3295595 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : ((term1022 _86360 x r p q) = (term1023 _86360 x r p q)) = ((term1018 _86360 x r p q) = (term1033 _86360 x r p q)).
Proof. exact (MK_COMB (@lem3295588 _86360 x r p q) (@lem3295594 _86360 x r p q)). Qed.
Lemma lem3295596 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1018 _86360 x r p q) = (term1033 _86360 x r p q).
Proof. exact (EQ_MP (@lem3295595 _86360 x r p q) (@lem3295580 _86360 x r p q)). Qed.
Lemma lem3295597 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1020 _86360 x p q) = (term1034 _86360 x p q).
Proof. exact (fun_ext (fun r : _86360 -> Prop => @lem3295596 _86360 x r p q)). Qed.
Lemma lem3295598 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295599 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1021 _86360 x p q) = (term1035 _86360 x p q).
Proof. exact (MK_COMB (@lem3295598 _86360) (@lem3295597 _86360 x p q)). Qed.
Lemma lem3295600 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1002 _86360 x p q) = (term1035 _86360 x p q).
Proof. exact (TRANS (@lem3295576 _86360 x p q) (@lem3295599 _86360 x p q)). Qed.
Lemma lem3295601 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1004 _86360 p q) = (term1036 _86360 p q).
Proof. exact (fun_ext (fun x : _86360 => @lem3295600 _86360 x p q)). Qed.
Lemma lem3295602 {_86360 : Type'} : (@ex _86360) = (@ex _86360).
Proof. exact (eq_refl (@ex _86360)). Qed.
Lemma lem3295603 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1005 _86360 p q) = (term1037 _86360 p q).
Proof. exact (MK_COMB (@lem3295602 _86360) (@lem3295601 _86360 p q)). Qed.
Lemma lem3295604 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term987 _86360 p q) = (term1037 _86360 p q).
Proof. exact (TRANS (@lem3295556 _86360 p q) (@lem3295603 _86360 p q)). Qed.
Lemma lem3295605 {_86360 : Type'} (q : _86360 -> Prop) : (term989 _86360 q) = (term1038 _86360 q).
Proof. exact (fun_ext (fun p : _86360 -> Prop => @lem3295604 _86360 p q)). Qed.
Lemma lem3295606 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295607 {_86360 : Type'} (q : _86360 -> Prop) : (term990 _86360 q) = (term1039 _86360 q).
Proof. exact (MK_COMB (@lem3295606 _86360) (@lem3295605 _86360 q)). Qed.
Lemma lem3295608 {_86360 : Type'} (q : _86360 -> Prop) : (term969 _86360 q) = (term1039 _86360 q).
Proof. exact (TRANS (@lem3295530 _86360 q) (@lem3295607 _86360 q)). Qed.
Lemma lem3295609 {_86360 : Type'} : (term971 _86360) = (term1040 _86360).
Proof. exact (fun_ext (fun q : _86360 -> Prop => @lem3295608 _86360 q)). Qed.
Lemma lem3295610 {_86360 : Type'} : (@ex (_86360 -> Prop)) = (@ex (_86360 -> Prop)).
Proof. exact (eq_refl (@ex (_86360 -> Prop))). Qed.
Lemma lem3295611 {_86360 : Type'} : (term972 _86360) = (term1041 _86360).
Proof. exact (MK_COMB (@lem3295610 _86360) (@lem3295609 _86360)). Qed.
Lemma lem3295612 {_86360 : Type'} : (term954 _86360) = (term1041 _86360).
Proof. exact (TRANS (@lem3295503 _86360) (@lem3295611 _86360)). Qed.
Lemma lem3295613 {_86360 : Type'} : (term767 _86360) = (term1041 _86360).
Proof. exact (TRANS (@lem3295476 _86360) (@lem3295612 _86360)). Qed.
Lemma lem3295614 {_86360 : Type'} : (term457 _86360) = (term1041 _86360).
Proof. exact (TRANS (@lem3294808 _86360) (@lem3295613 _86360)). Qed.
Lemma lem3295615 {_86360 : Type'} : (term289 _86360) = (term1041 _86360).
Proof. exact (TRANS (@lem3292853 _86360) (@lem3295614 _86360)). Qed.
Lemma lem3295616 {_86360 : Type'} (h1 : term289 _86360) : term1041 _86360.
Proof. exact (EQ_MP (@lem3295615 _86360) (@lem3292508 _86360 h1)). Qed.
Lemma lem3295617 {_86360 : Type'} (q : _86360 -> Prop) (h1 : term1039 _86360 q) : term1039 _86360 q.
Proof. exact (h1). Qed.
Lemma lem3295618 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term1037 _86360 p q) : term1037 _86360 p q.
Proof. exact (h1). Qed.
Lemma lem3295619 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term1035 _86360 x p q) : term1035 _86360 x p q.
Proof. exact (h1). Qed.
Lemma lem3295620 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term1033 _86360 x r p q) : term1033 _86360 x r p q.
Proof. exact (h1). Qed.
Lemma lem3295913 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term1030 _86360 x r p q x') : term1030 _86360 x r p q x'.
Proof. exact (h1). Qed.
Lemma lem3295914 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term301 _86360 q p x) : term301 _86360 q p x.
Proof. exact (h1). Qed.
Lemma lem3295915 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term944 _86360 r p q x') : term944 _86360 r p q x'.
Proof. exact (h1). Qed.
Lemma lem3295916 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : term297 _86360 q p x.
Proof. exact (h1). Qed.
Lemma lem3295917 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : term295 _86360 q p x.
Proof. exact (h1). Qed.
Lemma lem3295918 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : term291 _86360 q p x.
Proof. exact (proj2 (@lem3295916 _86360 q p x h1)). Qed.
Lemma lem3295919 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : term29 _86360 p q x.
Proof. exact (proj1 (@lem3295916 _86360 q p x h1)). Qed.
Lemma lem3295924 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : term29 _86360 q p x.
Proof. exact (proj2 (@lem3295917 _86360 q p x h1)). Qed.
Lemma lem3295925 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : term291 _86360 p q x.
Proof. exact (proj1 (@lem3295917 _86360 q p x h1)). Qed.
Lemma lem3295930 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term346 _86360 p q r x') : term346 _86360 p q r x'.
Proof. exact (h1). Qed.
Lemma lem3295931 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term865 _86360 r p q x') : term865 _86360 r p q x'.
Proof. exact (h1). Qed.
Lemma lem3295932 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term342 _86360 p q r x'.
Proof. exact (h1). Qed.
Lemma lem3295933 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term339 _86360 p q r x'.
Proof. exact (h1). Qed.
Lemma lem3295934 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term334 _86360 p q r x'.
Proof. exact (proj2 (@lem3295932 _86360 p q r x' h1)). Qed.
Lemma lem3295935 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term40 _86360 p q r x'.
Proof. exact (proj1 (@lem3295932 _86360 p q r x' h1)). Qed.
Lemma lem3295937 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term29 _86360 p q x'.
Proof. exact (proj1 (@lem3295935 _86360 p q r x' h1)). Qed.
Lemma lem3295941 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term291 _86360 q r x') : term291 _86360 q r x'.
Proof. exact (h1). Qed.
Lemma lem3295944 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term45 _86360 p q r x'.
Proof. exact (proj2 (@lem3295933 _86360 p q r x' h1)). Qed.
Lemma lem3295945 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term330 _86360 p q r x'.
Proof. exact (proj1 (@lem3295933 _86360 p q r x' h1)). Qed.
Lemma lem3295946 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term29 _86360 q r x'.
Proof. exact (proj2 (@lem3295944 _86360 p q r x' h1)). Qed.
Lemma lem3295950 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term291 _86360 p q x') : term291 _86360 p q x'.
Proof. exact (h1). Qed.
Lemma lem3295954 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term383 _86360 q p r x') : term383 _86360 q p r x'.
Proof. exact (h1). Qed.
Lemma lem3295955 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term423 _86360 p q x') : term423 _86360 p q x'.
Proof. exact (h1). Qed.
Lemma lem3295956 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term379 _86360 q p r x'.
Proof. exact (h1). Qed.
Lemma lem3295957 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term376 _86360 q p r x'.
Proof. exact (h1). Qed.
Lemma lem3295958 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term334 _86360 q p r x'.
Proof. exact (proj2 (@lem3295956 _86360 q p r x' h1)). Qed.
Lemma lem3295959 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term45 _86360 p q r x'.
Proof. exact (proj1 (@lem3295956 _86360 q p r x' h1)). Qed.
Lemma lem3295960 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term29 _86360 q r x'.
Proof. exact (proj2 (@lem3295959 _86360 q p r x' h1)). Qed.
Lemma lem3295965 {_86360 : Type'} (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term291 _86360 p r x') : term291 _86360 p r x'.
Proof. exact (h1). Qed.
Lemma lem3295968 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term45 _86360 q p r x'.
Proof. exact (proj2 (@lem3295957 _86360 q p r x' h1)). Qed.
Lemma lem3295969 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term334 _86360 p q r x'.
Proof. exact (proj1 (@lem3295957 _86360 q p r x' h1)). Qed.
Lemma lem3295970 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term29 _86360 p r x'.
Proof. exact (proj2 (@lem3295968 _86360 q p r x' h1)). Qed.
Lemma lem3295975 {_86360 : Type'} (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term291 _86360 q r x') : term291 _86360 q r x'.
Proof. exact (h1). Qed.
Lemma lem3295978 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : term419 _86360 p q x'.
Proof. exact (h1). Qed.
Lemma lem3295979 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : term416 _86360 p q x'.
Proof. exact (h1). Qed.
Lemma lem3295980 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : term291 _86360 p q x'.
Proof. exact (proj2 (@lem3295978 _86360 p q x' h1)). Qed.
Lemma lem3295981 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : term66 _86360 p q x'.
Proof. exact (proj1 (@lem3295978 _86360 p q x' h1)). Qed.
Lemma lem3295982 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : term29 _86360 p q x'.
Proof. exact (proj2 (@lem3295981 _86360 p q x' h1)). Qed.
Lemma lem3295988 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : term29 _86360 p q x'.
Proof. exact (proj2 (@lem3295979 _86360 p q x' h1)). Qed.
Lemma lem3295989 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : term411 _86360 p q x'.
Proof. exact (proj1 (@lem3295979 _86360 p q x' h1)). Qed.
Lemma lem3295993 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term291 _86360 p q x') : term291 _86360 p q x'.
Proof. exact (h1). Qed.
Lemma lem3296007 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) : term326 _86360 q x.
Proof. exact (h1). Qed.
Lemma lem3296019 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) : term326 _86360 p x.
Proof. exact (h1). Qed.
Lemma lem3296031 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) : term326 _86360 p x.
Proof. exact (h1). Qed.
Lemma lem3296043 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) : term326 _86360 q x.
Proof. exact (h1). Qed.
Lemma lem3296059 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296075 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296091 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296107 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296123 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296139 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296155 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296171 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296187 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296203 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296219 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296235 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296251 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296267 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296279 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296291 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296303 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296309 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) : term326 _86360 q x.
Proof. exact (h1). Qed.
Lemma lem3296315 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) : term326 _86360 p x.
Proof. exact (h1). Qed.
Lemma lem3296321 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) : term326 _86360 p x.
Proof. exact (h1). Qed.
Lemma lem3296327 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) : term326 _86360 q x.
Proof. exact (h1). Qed.
Lemma lem3296335 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296343 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296351 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296359 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296367 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296375 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296383 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296391 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296399 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296407 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296415 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296423 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term326 _86360 r x'.
Proof. exact (h1). Qed.
Lemma lem3296431 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296439 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296445 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296451 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term326 _86360 p x'.
Proof. exact (h1). Qed.
Lemma lem3296457 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term326 _86360 q x'.
Proof. exact (h1). Qed.
Lemma lem3296459 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : q x.
Proof. exact (proj2 (@lem3295919 _86360 q p x h1)). Qed.
Lemma lem3296460 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : term1042 _86360 q x.
Proof. exact (fun h0 : term326 _86360 q x => @lem3296459 _86360 q p x h1). Qed.
Lemma lem3296462 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296463 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term1042 _86360 q x) = (q x).
Proof. exact (@lem3296462 (q x)). Qed.
Lemma lem3296464 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : q x.
Proof. exact (EQ_MP (@lem3296463 _86360 q x) (@lem3296460 _86360 q p x h1)). Qed.
Lemma lem3296467 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296469 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term326 _86360 q x) = (term1044 _86360 q x).
Proof. exact (@lem3296467 (q x)). Qed.
Lemma lem3296472 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) : term1044 _86360 q x.
Proof. exact (EQ_MP (@lem3296469 _86360 q x) (@lem3296309 _86360 q x h1)). Qed.
Lemma lem3296475 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : False.
Proof. exact (@lem3296472 _86360 q x h1 (@lem3296464 _86360 q p x h2)). Qed.
Lemma lem3296476 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : term1045.
Proof. exact (fun h0 : ~ False => @lem3296475 _86360 q p x h1 h2). Qed.
Lemma lem3296478 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296479 : term1045 = False.
Proof. exact (@lem3296478 False). Qed.
Lemma lem3296480 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296479) (@lem3296476 _86360 q p x h1 h2)). Qed.
Lemma lem3296482 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : p x.
Proof. exact (proj1 (@lem3295919 _86360 q p x h1)). Qed.
Lemma lem3296483 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : term1042 _86360 p x.
Proof. exact (fun h0 : term326 _86360 p x => @lem3296482 _86360 q p x h1). Qed.
Lemma lem3296485 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296486 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term1042 _86360 p x) = (p x).
Proof. exact (@lem3296485 (p x)). Qed.
Lemma lem3296487 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : p x.
Proof. exact (EQ_MP (@lem3296486 _86360 p x) (@lem3296483 _86360 q p x h1)). Qed.
Lemma lem3296490 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296492 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term326 _86360 p x) = (term1044 _86360 p x).
Proof. exact (@lem3296490 (p x)). Qed.
Lemma lem3296495 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) : term1044 _86360 p x.
Proof. exact (EQ_MP (@lem3296492 _86360 p x) (@lem3296315 _86360 p x h1)). Qed.
Lemma lem3296498 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : False.
Proof. exact (@lem3296495 _86360 p x h1 (@lem3296487 _86360 q p x h2)). Qed.
Lemma lem3296499 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : term1045.
Proof. exact (fun h0 : ~ False => @lem3296498 _86360 q p x h1 h2). Qed.
Lemma lem3296501 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296502 : term1045 = False.
Proof. exact (@lem3296501 False). Qed.
Lemma lem3296503 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296502) (@lem3296499 _86360 q p x h1 h2)). Qed.
Lemma lem3296505 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : p x.
Proof. exact (proj2 (@lem3295924 _86360 q p x h1)). Qed.
Lemma lem3296506 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : term1042 _86360 p x.
Proof. exact (fun h0 : term326 _86360 p x => @lem3296505 _86360 q p x h1). Qed.
Lemma lem3296508 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296509 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term1042 _86360 p x) = (p x).
Proof. exact (@lem3296508 (p x)). Qed.
Lemma lem3296510 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : p x.
Proof. exact (EQ_MP (@lem3296509 _86360 p x) (@lem3296506 _86360 q p x h1)). Qed.
Lemma lem3296513 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296515 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) : (term326 _86360 p x) = (term1044 _86360 p x).
Proof. exact (@lem3296513 (p x)). Qed.
Lemma lem3296518 {_86360 : Type'} (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) : term1044 _86360 p x.
Proof. exact (EQ_MP (@lem3296515 _86360 p x) (@lem3296321 _86360 p x h1)). Qed.
Lemma lem3296521 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : False.
Proof. exact (@lem3296518 _86360 p x h1 (@lem3296510 _86360 q p x h2)). Qed.
Lemma lem3296522 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : term1045.
Proof. exact (fun h0 : ~ False => @lem3296521 _86360 q p x h1 h2). Qed.
Lemma lem3296524 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296525 : term1045 = False.
Proof. exact (@lem3296524 False). Qed.
Lemma lem3296526 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296525) (@lem3296522 _86360 q p x h1 h2)). Qed.
Lemma lem3296528 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : q x.
Proof. exact (proj1 (@lem3295924 _86360 q p x h1)). Qed.
Lemma lem3296529 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : term1042 _86360 q x.
Proof. exact (fun h0 : term326 _86360 q x => @lem3296528 _86360 q p x h1). Qed.
Lemma lem3296531 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296532 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term1042 _86360 q x) = (q x).
Proof. exact (@lem3296531 (q x)). Qed.
Lemma lem3296533 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : q x.
Proof. exact (EQ_MP (@lem3296532 _86360 q x) (@lem3296529 _86360 q p x h1)). Qed.
Lemma lem3296536 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296538 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) : (term326 _86360 q x) = (term1044 _86360 q x).
Proof. exact (@lem3296536 (q x)). Qed.
Lemma lem3296541 {_86360 : Type'} (q : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) : term1044 _86360 q x.
Proof. exact (EQ_MP (@lem3296538 _86360 q x) (@lem3296327 _86360 q x h1)). Qed.
Lemma lem3296544 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : False.
Proof. exact (@lem3296541 _86360 q x h1 (@lem3296533 _86360 q p x h2)). Qed.
Lemma lem3296545 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : term1045.
Proof. exact (fun h0 : ~ False => @lem3296544 _86360 q p x h1 h2). Qed.
Lemma lem3296547 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296548 : term1045 = False.
Proof. exact (@lem3296547 False). Qed.
Lemma lem3296549 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296548) (@lem3296545 _86360 q p x h1 h2)). Qed.
Lemma lem3296551 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : p x'.
Proof. exact (proj1 (@lem3295937 _86360 p q r x' h1)). Qed.
Lemma lem3296552 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296551 _86360 p q r x' h1). Qed.
Lemma lem3296554 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296555 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296554 (p x')). Qed.
Lemma lem3296556 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : p x'.
Proof. exact (EQ_MP (@lem3296555 _86360 p x') (@lem3296552 _86360 p q r x' h1)). Qed.
Lemma lem3296559 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296561 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296559 (p x')). Qed.
Lemma lem3296564 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296561 _86360 p x') (@lem3296335 _86360 p x' h1)). Qed.
Lemma lem3296567 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (@lem3296564 _86360 p x' h1 (@lem3296556 _86360 p q r x' h2)). Qed.
Lemma lem3296568 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296567 _86360 p q r x' h1 h2). Qed.
Lemma lem3296570 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296571 : term1045 = False.
Proof. exact (@lem3296570 False). Qed.
Lemma lem3296572 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296571) (@lem3296568 _86360 p q r x' h1 h2)). Qed.
Lemma lem3296574 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : q x'.
Proof. exact (proj2 (@lem3295937 _86360 p q r x' h1)). Qed.
Lemma lem3296575 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term1042 _86360 q x'.
Proof. exact (fun h0 : term326 _86360 q x' => @lem3296574 _86360 p q r x' h1). Qed.
Lemma lem3296577 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296578 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term1042 _86360 q x') = (q x').
Proof. exact (@lem3296577 (q x')). Qed.
Lemma lem3296579 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : q x'.
Proof. exact (EQ_MP (@lem3296578 _86360 q x') (@lem3296575 _86360 p q r x' h1)). Qed.
Lemma lem3296582 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296584 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term326 _86360 q x') = (term1044 _86360 q x').
Proof. exact (@lem3296582 (q x')). Qed.
Lemma lem3296587 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term1044 _86360 q x'.
Proof. exact (EQ_MP (@lem3296584 _86360 q x') (@lem3296343 _86360 q x' h1)). Qed.
Lemma lem3296590 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (@lem3296587 _86360 q x' h1 (@lem3296579 _86360 p q r x' h2)). Qed.
Lemma lem3296591 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296590 _86360 p q r x' h1 h2). Qed.
Lemma lem3296593 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296594 : term1045 = False.
Proof. exact (@lem3296593 False). Qed.
Lemma lem3296595 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296594) (@lem3296591 _86360 p q r x' h1 h2)). Qed.
Lemma lem3296597 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : r x'.
Proof. exact (proj2 (@lem3295935 _86360 p q r x' h1)). Qed.
Lemma lem3296598 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : term1042 _86360 r x'.
Proof. exact (fun h0 : term326 _86360 r x' => @lem3296597 _86360 p q r x' h1). Qed.
Lemma lem3296600 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296601 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term1042 _86360 r x') = (r x').
Proof. exact (@lem3296600 (r x')). Qed.
Lemma lem3296602 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : r x'.
Proof. exact (EQ_MP (@lem3296601 _86360 r x') (@lem3296598 _86360 p q r x' h1)). Qed.
Lemma lem3296605 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296607 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term326 _86360 r x') = (term1044 _86360 r x').
Proof. exact (@lem3296605 (r x')). Qed.
Lemma lem3296610 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term1044 _86360 r x'.
Proof. exact (EQ_MP (@lem3296607 _86360 r x') (@lem3296351 _86360 r x' h1)). Qed.
Lemma lem3296613 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (@lem3296610 _86360 r x' h1 (@lem3296602 _86360 p q r x' h2)). Qed.
Lemma lem3296614 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296613 _86360 p q r x' h1 h2). Qed.
Lemma lem3296616 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296617 : term1045 = False.
Proof. exact (@lem3296616 False). Qed.
Lemma lem3296618 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296617) (@lem3296614 _86360 p q r x' h1 h2)). Qed.
Lemma lem3296620 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : p x'.
Proof. exact (proj1 (@lem3295944 _86360 p q r x' h1)). Qed.
Lemma lem3296621 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296620 _86360 p q r x' h1). Qed.
Lemma lem3296623 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296624 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296623 (p x')). Qed.
Lemma lem3296625 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : p x'.
Proof. exact (EQ_MP (@lem3296624 _86360 p x') (@lem3296621 _86360 p q r x' h1)). Qed.
Lemma lem3296628 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296630 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296628 (p x')). Qed.
Lemma lem3296633 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296630 _86360 p x') (@lem3296359 _86360 p x' h1)). Qed.
Lemma lem3296636 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (@lem3296633 _86360 p x' h1 (@lem3296625 _86360 p q r x' h2)). Qed.
Lemma lem3296637 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296636 _86360 p q r x' h1 h2). Qed.
Lemma lem3296639 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296640 : term1045 = False.
Proof. exact (@lem3296639 False). Qed.
Lemma lem3296641 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296640) (@lem3296637 _86360 p q r x' h1 h2)). Qed.
Lemma lem3296643 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : q x'.
Proof. exact (proj1 (@lem3295946 _86360 p q r x' h1)). Qed.
Lemma lem3296644 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term1042 _86360 q x'.
Proof. exact (fun h0 : term326 _86360 q x' => @lem3296643 _86360 p q r x' h1). Qed.
Lemma lem3296646 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296647 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term1042 _86360 q x') = (q x').
Proof. exact (@lem3296646 (q x')). Qed.
Lemma lem3296648 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : q x'.
Proof. exact (EQ_MP (@lem3296647 _86360 q x') (@lem3296644 _86360 p q r x' h1)). Qed.
Lemma lem3296651 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296653 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term326 _86360 q x') = (term1044 _86360 q x').
Proof. exact (@lem3296651 (q x')). Qed.
Lemma lem3296656 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term1044 _86360 q x'.
Proof. exact (EQ_MP (@lem3296653 _86360 q x') (@lem3296367 _86360 q x' h1)). Qed.
Lemma lem3296659 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (@lem3296656 _86360 q x' h1 (@lem3296648 _86360 p q r x' h2)). Qed.
Lemma lem3296660 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296659 _86360 p q r x' h1 h2). Qed.
Lemma lem3296662 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296663 : term1045 = False.
Proof. exact (@lem3296662 False). Qed.
Lemma lem3296664 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296663) (@lem3296660 _86360 p q r x' h1 h2)). Qed.
Lemma lem3296666 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : r x'.
Proof. exact (proj2 (@lem3295946 _86360 p q r x' h1)). Qed.
Lemma lem3296667 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : term1042 _86360 r x'.
Proof. exact (fun h0 : term326 _86360 r x' => @lem3296666 _86360 p q r x' h1). Qed.
Lemma lem3296669 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296670 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term1042 _86360 r x') = (r x').
Proof. exact (@lem3296669 (r x')). Qed.
Lemma lem3296671 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : r x'.
Proof. exact (EQ_MP (@lem3296670 _86360 r x') (@lem3296667 _86360 p q r x' h1)). Qed.
Lemma lem3296674 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296676 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term326 _86360 r x') = (term1044 _86360 r x').
Proof. exact (@lem3296674 (r x')). Qed.
Lemma lem3296679 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term1044 _86360 r x'.
Proof. exact (EQ_MP (@lem3296676 _86360 r x') (@lem3296375 _86360 r x' h1)). Qed.
Lemma lem3296682 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (@lem3296679 _86360 r x' h1 (@lem3296671 _86360 p q r x' h2)). Qed.
Lemma lem3296683 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296682 _86360 p q r x' h1 h2). Qed.
Lemma lem3296685 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296686 : term1045 = False.
Proof. exact (@lem3296685 False). Qed.
Lemma lem3296687 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296686) (@lem3296683 _86360 p q r x' h1 h2)). Qed.
Lemma lem3296689 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : q x'.
Proof. exact (proj1 (@lem3295960 _86360 q p r x' h1)). Qed.
Lemma lem3296690 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term1042 _86360 q x'.
Proof. exact (fun h0 : term326 _86360 q x' => @lem3296689 _86360 q p r x' h1). Qed.
Lemma lem3296692 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296693 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term1042 _86360 q x') = (q x').
Proof. exact (@lem3296692 (q x')). Qed.
Lemma lem3296694 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : q x'.
Proof. exact (EQ_MP (@lem3296693 _86360 q x') (@lem3296690 _86360 q p r x' h1)). Qed.
Lemma lem3296697 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296699 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term326 _86360 q x') = (term1044 _86360 q x').
Proof. exact (@lem3296697 (q x')). Qed.
Lemma lem3296702 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term1044 _86360 q x'.
Proof. exact (EQ_MP (@lem3296699 _86360 q x') (@lem3296383 _86360 q x' h1)). Qed.
Lemma lem3296705 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (@lem3296702 _86360 q x' h1 (@lem3296694 _86360 q p r x' h2)). Qed.
Lemma lem3296706 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296705 _86360 q p r x' h1 h2). Qed.
Lemma lem3296708 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296709 : term1045 = False.
Proof. exact (@lem3296708 False). Qed.
Lemma lem3296710 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296709) (@lem3296706 _86360 q p r x' h1 h2)). Qed.
Lemma lem3296712 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : p x'.
Proof. exact (proj1 (@lem3295959 _86360 q p r x' h1)). Qed.
Lemma lem3296713 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296712 _86360 q p r x' h1). Qed.
Lemma lem3296715 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296716 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296715 (p x')). Qed.
Lemma lem3296717 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : p x'.
Proof. exact (EQ_MP (@lem3296716 _86360 p x') (@lem3296713 _86360 q p r x' h1)). Qed.
Lemma lem3296720 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296722 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296720 (p x')). Qed.
Lemma lem3296725 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296722 _86360 p x') (@lem3296391 _86360 p x' h1)). Qed.
Lemma lem3296728 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (@lem3296725 _86360 p x' h1 (@lem3296717 _86360 q p r x' h2)). Qed.
Lemma lem3296729 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296728 _86360 q p r x' h1 h2). Qed.
Lemma lem3296731 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296732 : term1045 = False.
Proof. exact (@lem3296731 False). Qed.
Lemma lem3296733 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296732) (@lem3296729 _86360 q p r x' h1 h2)). Qed.
Lemma lem3296735 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : r x'.
Proof. exact (proj2 (@lem3295960 _86360 q p r x' h1)). Qed.
Lemma lem3296736 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : term1042 _86360 r x'.
Proof. exact (fun h0 : term326 _86360 r x' => @lem3296735 _86360 q p r x' h1). Qed.
Lemma lem3296738 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296739 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term1042 _86360 r x') = (r x').
Proof. exact (@lem3296738 (r x')). Qed.
Lemma lem3296740 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : r x'.
Proof. exact (EQ_MP (@lem3296739 _86360 r x') (@lem3296736 _86360 q p r x' h1)). Qed.
Lemma lem3296743 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296745 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term326 _86360 r x') = (term1044 _86360 r x').
Proof. exact (@lem3296743 (r x')). Qed.
Lemma lem3296748 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term1044 _86360 r x'.
Proof. exact (EQ_MP (@lem3296745 _86360 r x') (@lem3296399 _86360 r x' h1)). Qed.
Lemma lem3296751 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (@lem3296748 _86360 r x' h1 (@lem3296740 _86360 q p r x' h2)). Qed.
Lemma lem3296752 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296751 _86360 q p r x' h1 h2). Qed.
Lemma lem3296754 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296755 : term1045 = False.
Proof. exact (@lem3296754 False). Qed.
Lemma lem3296756 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296755) (@lem3296752 _86360 q p r x' h1 h2)). Qed.
Lemma lem3296758 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : p x'.
Proof. exact (proj1 (@lem3295970 _86360 q p r x' h1)). Qed.
Lemma lem3296759 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296758 _86360 q p r x' h1). Qed.
Lemma lem3296761 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296762 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296761 (p x')). Qed.
Lemma lem3296763 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : p x'.
Proof. exact (EQ_MP (@lem3296762 _86360 p x') (@lem3296759 _86360 q p r x' h1)). Qed.
Lemma lem3296766 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296768 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296766 (p x')). Qed.
Lemma lem3296771 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296768 _86360 p x') (@lem3296407 _86360 p x' h1)). Qed.
Lemma lem3296774 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (@lem3296771 _86360 p x' h1 (@lem3296763 _86360 q p r x' h2)). Qed.
Lemma lem3296775 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296774 _86360 q p r x' h1 h2). Qed.
Lemma lem3296777 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296778 : term1045 = False.
Proof. exact (@lem3296777 False). Qed.
Lemma lem3296779 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296778) (@lem3296775 _86360 q p r x' h1 h2)). Qed.
Lemma lem3296781 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : q x'.
Proof. exact (proj1 (@lem3295968 _86360 q p r x' h1)). Qed.
Lemma lem3296782 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term1042 _86360 q x'.
Proof. exact (fun h0 : term326 _86360 q x' => @lem3296781 _86360 q p r x' h1). Qed.
Lemma lem3296784 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296785 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term1042 _86360 q x') = (q x').
Proof. exact (@lem3296784 (q x')). Qed.
Lemma lem3296786 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : q x'.
Proof. exact (EQ_MP (@lem3296785 _86360 q x') (@lem3296782 _86360 q p r x' h1)). Qed.
Lemma lem3296789 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296791 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term326 _86360 q x') = (term1044 _86360 q x').
Proof. exact (@lem3296789 (q x')). Qed.
Lemma lem3296794 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term1044 _86360 q x'.
Proof. exact (EQ_MP (@lem3296791 _86360 q x') (@lem3296415 _86360 q x' h1)). Qed.
Lemma lem3296797 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (@lem3296794 _86360 q x' h1 (@lem3296786 _86360 q p r x' h2)). Qed.
Lemma lem3296798 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296797 _86360 q p r x' h1 h2). Qed.
Lemma lem3296800 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296801 : term1045 = False.
Proof. exact (@lem3296800 False). Qed.
Lemma lem3296802 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296801) (@lem3296798 _86360 q p r x' h1 h2)). Qed.
Lemma lem3296804 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : r x'.
Proof. exact (proj2 (@lem3295970 _86360 q p r x' h1)). Qed.
Lemma lem3296805 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : term1042 _86360 r x'.
Proof. exact (fun h0 : term326 _86360 r x' => @lem3296804 _86360 q p r x' h1). Qed.
Lemma lem3296807 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296808 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term1042 _86360 r x') = (r x').
Proof. exact (@lem3296807 (r x')). Qed.
Lemma lem3296809 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : r x'.
Proof. exact (EQ_MP (@lem3296808 _86360 r x') (@lem3296805 _86360 q p r x' h1)). Qed.
Lemma lem3296812 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296814 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) : (term326 _86360 r x') = (term1044 _86360 r x').
Proof. exact (@lem3296812 (r x')). Qed.
Lemma lem3296817 {_86360 : Type'} (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') : term1044 _86360 r x'.
Proof. exact (EQ_MP (@lem3296814 _86360 r x') (@lem3296423 _86360 r x' h1)). Qed.
Lemma lem3296820 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (@lem3296817 _86360 r x' h1 (@lem3296809 _86360 q p r x' h2)). Qed.
Lemma lem3296821 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296820 _86360 q p r x' h1 h2). Qed.
Lemma lem3296823 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296824 : term1045 = False.
Proof. exact (@lem3296823 False). Qed.
Lemma lem3296825 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296824) (@lem3296821 _86360 q p r x' h1 h2)). Qed.
Lemma lem3296827 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : p x'.
Proof. exact (proj1 (@lem3295981 _86360 p q x' h1)). Qed.
Lemma lem3296828 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296827 _86360 p q x' h1). Qed.
Lemma lem3296830 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296831 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296830 (p x')). Qed.
Lemma lem3296832 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : p x'.
Proof. exact (EQ_MP (@lem3296831 _86360 p x') (@lem3296828 _86360 p q x' h1)). Qed.
Lemma lem3296835 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296837 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296835 (p x')). Qed.
Lemma lem3296840 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296837 _86360 p x') (@lem3296431 _86360 p x' h1)). Qed.
Lemma lem3296843 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : False.
Proof. exact (@lem3296840 _86360 p x' h1 (@lem3296832 _86360 p q x' h2)). Qed.
Lemma lem3296844 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296843 _86360 p q x' h1 h2). Qed.
Lemma lem3296846 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296847 : term1045 = False.
Proof. exact (@lem3296846 False). Qed.
Lemma lem3296848 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296847) (@lem3296844 _86360 p q x' h1 h2)). Qed.
Lemma lem3296850 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : q x'.
Proof. exact (proj2 (@lem3295982 _86360 p q x' h1)). Qed.
Lemma lem3296851 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : term1042 _86360 q x'.
Proof. exact (fun h0 : term326 _86360 q x' => @lem3296850 _86360 p q x' h1). Qed.
Lemma lem3296853 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296854 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term1042 _86360 q x') = (q x').
Proof. exact (@lem3296853 (q x')). Qed.
Lemma lem3296855 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : q x'.
Proof. exact (EQ_MP (@lem3296854 _86360 q x') (@lem3296851 _86360 p q x' h1)). Qed.
Lemma lem3296858 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296860 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term326 _86360 q x') = (term1044 _86360 q x').
Proof. exact (@lem3296858 (q x')). Qed.
Lemma lem3296863 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term1044 _86360 q x'.
Proof. exact (EQ_MP (@lem3296860 _86360 q x') (@lem3296439 _86360 q x' h1)). Qed.
Lemma lem3296866 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : False.
Proof. exact (@lem3296863 _86360 q x' h1 (@lem3296855 _86360 p q x' h2)). Qed.
Lemma lem3296867 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296866 _86360 p q x' h1 h2). Qed.
Lemma lem3296869 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296870 : term1045 = False.
Proof. exact (@lem3296869 False). Qed.
Lemma lem3296871 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296870) (@lem3296867 _86360 p q x' h1 h2)). Qed.
Lemma lem3296873 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : p x'.
Proof. exact (proj1 (@lem3295988 _86360 p q x' h1)). Qed.
Lemma lem3296874 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296873 _86360 p q x' h1). Qed.
Lemma lem3296876 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296877 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296876 (p x')). Qed.
Lemma lem3296878 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : p x'.
Proof. exact (EQ_MP (@lem3296877 _86360 p x') (@lem3296874 _86360 p q x' h1)). Qed.
Lemma lem3296881 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296883 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296881 (p x')). Qed.
Lemma lem3296886 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296883 _86360 p x') (@lem3296445 _86360 p x' h1)). Qed.
Lemma lem3296889 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (@lem3296886 _86360 p x' h1 (@lem3296878 _86360 p q x' h2)). Qed.
Lemma lem3296890 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296889 _86360 p q x' h1 h2). Qed.
Lemma lem3296892 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296893 : term1045 = False.
Proof. exact (@lem3296892 False). Qed.
Lemma lem3296894 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296893) (@lem3296890 _86360 p q x' h1 h2)). Qed.
Lemma lem3296896 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : p x'.
Proof. exact (proj1 (@lem3295988 _86360 p q x' h1)). Qed.
Lemma lem3296897 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : term1042 _86360 p x'.
Proof. exact (fun h0 : term326 _86360 p x' => @lem3296896 _86360 p q x' h1). Qed.
Lemma lem3296899 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296900 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term1042 _86360 p x') = (p x').
Proof. exact (@lem3296899 (p x')). Qed.
Lemma lem3296901 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : p x'.
Proof. exact (EQ_MP (@lem3296900 _86360 p x') (@lem3296897 _86360 p q x' h1)). Qed.
Lemma lem3296904 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296906 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) : (term326 _86360 p x') = (term1044 _86360 p x').
Proof. exact (@lem3296904 (p x')). Qed.
Lemma lem3296909 {_86360 : Type'} (p : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') : term1044 _86360 p x'.
Proof. exact (EQ_MP (@lem3296906 _86360 p x') (@lem3296451 _86360 p x' h1)). Qed.
Lemma lem3296912 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (@lem3296909 _86360 p x' h1 (@lem3296901 _86360 p q x' h2)). Qed.
Lemma lem3296913 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296912 _86360 p q x' h1 h2). Qed.
Lemma lem3296915 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296916 : term1045 = False.
Proof. exact (@lem3296915 False). Qed.
Lemma lem3296917 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296916) (@lem3296913 _86360 p q x' h1 h2)). Qed.
Lemma lem3296919 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : q x'.
Proof. exact (proj2 (@lem3295988 _86360 p q x' h1)). Qed.
Lemma lem3296920 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : term1042 _86360 q x'.
Proof. exact (fun h0 : term326 _86360 q x' => @lem3296919 _86360 p q x' h1). Qed.
Lemma lem3296922 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296923 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term1042 _86360 q x') = (q x').
Proof. exact (@lem3296922 (q x')). Qed.
Lemma lem3296924 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : q x'.
Proof. exact (EQ_MP (@lem3296923 _86360 q x') (@lem3296920 _86360 p q x' h1)). Qed.
Lemma lem3296927 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3296929 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) : (term326 _86360 q x') = (term1044 _86360 q x').
Proof. exact (@lem3296927 (q x')). Qed.
Lemma lem3296932 {_86360 : Type'} (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') : term1044 _86360 q x'.
Proof. exact (EQ_MP (@lem3296929 _86360 q x') (@lem3296457 _86360 q x' h1)). Qed.
Lemma lem3296935 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : False.
Proof. exact (@lem3296932 _86360 q x' h1 (@lem3296924 _86360 p q x' h2)). Qed.
Lemma lem3296936 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : term1045.
Proof. exact (fun h0 : ~ False => @lem3296935 _86360 p q x' h1 h2). Qed.
Lemma lem3296938 (p : Prop) : (term1043 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3296939 : term1045 = False.
Proof. exact (@lem3296938 False). Qed.
Lemma lem3296940 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296939) (@lem3296936 _86360 p q x' h1 h2)). Qed.
Lemma lem3296941 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296940 _86360 p q x' h1 h2) (fun h3 : False => @lem3296457 _86360 q x' h1)). Qed.
Lemma lem3296942 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296941 _86360 p q x' h1 h2) (@lem3296457 _86360 q x' h1)). Qed.
Lemma lem3296943 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296917 _86360 p q x' h1 h2) (fun h3 : False => @lem3296451 _86360 p x' h1)). Qed.
Lemma lem3296944 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296943 _86360 p q x' h1 h2) (@lem3296451 _86360 p x' h1)). Qed.
Lemma lem3296945 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296894 _86360 p q x' h1 h2) (fun h3 : False => @lem3296445 _86360 p x' h1)). Qed.
Lemma lem3296946 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296945 _86360 p q x' h1 h2) (@lem3296445 _86360 p x' h1)). Qed.
Lemma lem3296947 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296871 _86360 p q x' h1 h2) (fun h3 : False => @lem3296439 _86360 q x' h1)). Qed.
Lemma lem3296948 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296947 _86360 p q x' h1 h2) (@lem3296439 _86360 q x' h1)). Qed.
Lemma lem3296949 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296848 _86360 p q x' h1 h2) (fun h3 : False => @lem3296431 _86360 p x' h1)). Qed.
Lemma lem3296950 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296949 _86360 p q x' h1 h2) (@lem3296431 _86360 p x' h1)). Qed.
Lemma lem3296951 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296825 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296423 _86360 r x' h1)). Qed.
Lemma lem3296952 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296951 _86360 q p r x' h1 h2) (@lem3296423 _86360 r x' h1)). Qed.
Lemma lem3296953 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296802 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296415 _86360 q x' h1)). Qed.
Lemma lem3296954 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296953 _86360 q p r x' h1 h2) (@lem3296415 _86360 q x' h1)). Qed.
Lemma lem3296955 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296779 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296407 _86360 p x' h1)). Qed.
Lemma lem3296956 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296955 _86360 q p r x' h1 h2) (@lem3296407 _86360 p x' h1)). Qed.
Lemma lem3296957 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296756 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296399 _86360 r x' h1)). Qed.
Lemma lem3296958 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296957 _86360 q p r x' h1 h2) (@lem3296399 _86360 r x' h1)). Qed.
Lemma lem3296959 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296733 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296391 _86360 p x' h1)). Qed.
Lemma lem3296960 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296959 _86360 q p r x' h1 h2) (@lem3296391 _86360 p x' h1)). Qed.
Lemma lem3296961 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296710 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296383 _86360 q x' h1)). Qed.
Lemma lem3296962 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296961 _86360 q p r x' h1 h2) (@lem3296383 _86360 q x' h1)). Qed.
Lemma lem3296963 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296687 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296375 _86360 r x' h1)). Qed.
Lemma lem3296964 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296963 _86360 p q r x' h1 h2) (@lem3296375 _86360 r x' h1)). Qed.
Lemma lem3296965 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296664 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296367 _86360 q x' h1)). Qed.
Lemma lem3296966 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296965 _86360 p q r x' h1 h2) (@lem3296367 _86360 q x' h1)). Qed.
Lemma lem3296967 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296641 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296359 _86360 p x' h1)). Qed.
Lemma lem3296968 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296967 _86360 p q r x' h1 h2) (@lem3296359 _86360 p x' h1)). Qed.
Lemma lem3296969 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296618 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296351 _86360 r x' h1)). Qed.
Lemma lem3296970 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296969 _86360 p q r x' h1 h2) (@lem3296351 _86360 r x' h1)). Qed.
Lemma lem3296971 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296595 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296343 _86360 q x' h1)). Qed.
Lemma lem3296972 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296971 _86360 p q r x' h1 h2) (@lem3296343 _86360 q x' h1)). Qed.
Lemma lem3296973 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296572 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296335 _86360 p x' h1)). Qed.
Lemma lem3296974 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3296973 _86360 p q r x' h1 h2) (@lem3296335 _86360 p x' h1)). Qed.
Lemma lem3296975 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : (term326 _86360 q x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x => @lem3296549 _86360 q p x h1 h2) (fun h3 : False => @lem3296327 _86360 q x h1)). Qed.
Lemma lem3296976 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296975 _86360 q p x h1 h2) (@lem3296327 _86360 q x h1)). Qed.
Lemma lem3296977 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : (term326 _86360 p x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x => @lem3296526 _86360 q p x h1 h2) (fun h3 : False => @lem3296321 _86360 p x h1)). Qed.
Lemma lem3296978 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296977 _86360 q p x h1 h2) (@lem3296321 _86360 p x h1)). Qed.
Lemma lem3296979 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : (term326 _86360 p x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x => @lem3296503 _86360 q p x h1 h2) (fun h3 : False => @lem3296315 _86360 p x h1)). Qed.
Lemma lem3296980 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296979 _86360 q p x h1 h2) (@lem3296315 _86360 p x h1)). Qed.
Lemma lem3296981 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : (term326 _86360 q x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x => @lem3296480 _86360 q p x h1 h2) (fun h3 : False => @lem3296309 _86360 q x h1)). Qed.
Lemma lem3296982 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3296981 _86360 q p x h1 h2) (@lem3296309 _86360 q x h1)). Qed.
Lemma lem3296983 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296942 _86360 p q x' h1 h2) (fun h3 : False => @lem3296303 _86360 q x' h1)). Qed.
Lemma lem3296984 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296983 _86360 p q x' h1 h2) (@lem3296303 _86360 q x' h1)). Qed.
Lemma lem3296985 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296944 _86360 p q x' h1 h2) (fun h3 : False => @lem3296291 _86360 p x' h1)). Qed.
Lemma lem3296986 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296985 _86360 p q x' h1 h2) (@lem3296291 _86360 p x' h1)). Qed.
Lemma lem3296987 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296946 _86360 p q x' h1 h2) (fun h3 : False => @lem3296279 _86360 p x' h1)). Qed.
Lemma lem3296988 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296987 _86360 p q x' h1 h2) (@lem3296279 _86360 p x' h1)). Qed.
Lemma lem3296989 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296948 _86360 p q x' h1 h2) (fun h3 : False => @lem3296267 _86360 q x' h1)). Qed.
Lemma lem3296990 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296989 _86360 p q x' h1 h2) (@lem3296267 _86360 q x' h1)). Qed.
Lemma lem3296991 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296950 _86360 p q x' h1 h2) (fun h3 : False => @lem3296251 _86360 p x' h1)). Qed.
Lemma lem3296992 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3296991 _86360 p q x' h1 h2) (@lem3296251 _86360 p x' h1)). Qed.
Lemma lem3296993 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296952 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296235 _86360 r x' h1)). Qed.
Lemma lem3296994 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296993 _86360 q p r x' h1 h2) (@lem3296235 _86360 r x' h1)). Qed.
Lemma lem3296995 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296954 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296219 _86360 q x' h1)). Qed.
Lemma lem3296996 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296995 _86360 q p r x' h1 h2) (@lem3296219 _86360 q x' h1)). Qed.
Lemma lem3296997 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296956 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296203 _86360 p x' h1)). Qed.
Lemma lem3296998 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296997 _86360 q p r x' h1 h2) (@lem3296203 _86360 p x' h1)). Qed.
Lemma lem3296999 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296958 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296187 _86360 r x' h1)). Qed.
Lemma lem3297000 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3296999 _86360 q p r x' h1 h2) (@lem3296187 _86360 r x' h1)). Qed.
Lemma lem3297001 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296960 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296171 _86360 p x' h1)). Qed.
Lemma lem3297002 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297001 _86360 q p r x' h1 h2) (@lem3296171 _86360 p x' h1)). Qed.
Lemma lem3297003 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296962 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296155 _86360 q x' h1)). Qed.
Lemma lem3297004 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297003 _86360 q p r x' h1 h2) (@lem3296155 _86360 q x' h1)). Qed.
Lemma lem3297005 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296964 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296139 _86360 r x' h1)). Qed.
Lemma lem3297006 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297005 _86360 p q r x' h1 h2) (@lem3296139 _86360 r x' h1)). Qed.
Lemma lem3297007 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296966 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296123 _86360 q x' h1)). Qed.
Lemma lem3297008 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297007 _86360 p q r x' h1 h2) (@lem3296123 _86360 q x' h1)). Qed.
Lemma lem3297009 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296968 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296107 _86360 p x' h1)). Qed.
Lemma lem3297010 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297009 _86360 p q r x' h1 h2) (@lem3296107 _86360 p x' h1)). Qed.
Lemma lem3297011 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296970 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296091 _86360 r x' h1)). Qed.
Lemma lem3297012 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297011 _86360 p q r x' h1 h2) (@lem3296091 _86360 r x' h1)). Qed.
Lemma lem3297013 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296972 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296075 _86360 q x' h1)). Qed.
Lemma lem3297014 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297013 _86360 p q r x' h1 h2) (@lem3296075 _86360 q x' h1)). Qed.
Lemma lem3297015 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296974 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296059 _86360 p x' h1)). Qed.
Lemma lem3297016 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297015 _86360 p q r x' h1 h2) (@lem3296059 _86360 p x' h1)). Qed.
Lemma lem3297017 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : (term326 _86360 q x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x => @lem3296976 _86360 q p x h1 h2) (fun h3 : False => @lem3296043 _86360 q x h1)). Qed.
Lemma lem3297018 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297017 _86360 q p x h1 h2) (@lem3296043 _86360 q x h1)). Qed.
Lemma lem3297019 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : (term326 _86360 p x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x => @lem3296978 _86360 q p x h1 h2) (fun h3 : False => @lem3296031 _86360 p x h1)). Qed.
Lemma lem3297020 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297019 _86360 q p x h1 h2) (@lem3296031 _86360 p x h1)). Qed.
Lemma lem3297021 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : (term326 _86360 p x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x => @lem3296980 _86360 q p x h1 h2) (fun h3 : False => @lem3296019 _86360 p x h1)). Qed.
Lemma lem3297022 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297021 _86360 q p x h1 h2) (@lem3296019 _86360 p x h1)). Qed.
Lemma lem3297023 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : (term326 _86360 q x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x => @lem3296982 _86360 q p x h1 h2) (fun h3 : False => @lem3296007 _86360 q x h1)). Qed.
Lemma lem3297024 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297023 _86360 q p x h1 h2) (@lem3296007 _86360 q x h1)). Qed.
Lemma lem3297025 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296984 _86360 p q x' h1 h2) (fun h3 : False => @lem3296303 _86360 q x' h1)). Qed.
Lemma lem3297026 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3297025 _86360 p q x' h1 h2) (@lem3296303 _86360 q x' h1)). Qed.
Lemma lem3297027 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296986 _86360 p q x' h1 h2) (fun h3 : False => @lem3296291 _86360 p x' h1)). Qed.
Lemma lem3297028 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3297027 _86360 p q x' h1 h2) (@lem3296291 _86360 p x' h1)). Qed.
Lemma lem3297029 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296988 _86360 p q x' h1 h2) (fun h3 : False => @lem3296279 _86360 p x' h1)). Qed.
Lemma lem3297030 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term416 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3297029 _86360 p q x' h1 h2) (@lem3296279 _86360 p x' h1)). Qed.
Lemma lem3297031 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296990 _86360 p q x' h1 h2) (fun h3 : False => @lem3296267 _86360 q x' h1)). Qed.
Lemma lem3297032 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3297031 _86360 p q x' h1 h2) (@lem3296267 _86360 q x' h1)). Qed.
Lemma lem3297033 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296992 _86360 p q x' h1 h2) (fun h3 : False => @lem3296251 _86360 p x' h1)). Qed.
Lemma lem3297034 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term419 _86360 p q x') : False.
Proof. exact (EQ_MP (@lem3297033 _86360 p q x' h1 h2) (@lem3296251 _86360 p x' h1)). Qed.
Lemma lem3297035 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3296994 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296235 _86360 r x' h1)). Qed.
Lemma lem3297036 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297035 _86360 q p r x' h1 h2) (@lem3296235 _86360 r x' h1)). Qed.
Lemma lem3297037 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3296996 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296219 _86360 q x' h1)). Qed.
Lemma lem3297038 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297037 _86360 q p r x' h1 h2) (@lem3296219 _86360 q x' h1)). Qed.
Lemma lem3297039 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3296998 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296203 _86360 p x' h1)). Qed.
Lemma lem3297040 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term376 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297039 _86360 q p r x' h1 h2) (@lem3296203 _86360 p x' h1)). Qed.
Lemma lem3297041 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3297000 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296187 _86360 r x' h1)). Qed.
Lemma lem3297042 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297041 _86360 q p r x' h1 h2) (@lem3296187 _86360 r x' h1)). Qed.
Lemma lem3297043 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3297002 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296171 _86360 p x' h1)). Qed.
Lemma lem3297044 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297043 _86360 q p r x' h1 h2) (@lem3296171 _86360 p x' h1)). Qed.
Lemma lem3297045 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3297004 _86360 q p r x' h1 h2) (fun h3 : False => @lem3296155 _86360 q x' h1)). Qed.
Lemma lem3297046 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term379 _86360 q p r x') : False.
Proof. exact (EQ_MP (@lem3297045 _86360 q p r x' h1 h2) (@lem3296155 _86360 q x' h1)). Qed.
Lemma lem3297047 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3297006 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296139 _86360 r x' h1)). Qed.
Lemma lem3297048 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297047 _86360 p q r x' h1 h2) (@lem3296139 _86360 r x' h1)). Qed.
Lemma lem3297049 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3297008 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296123 _86360 q x' h1)). Qed.
Lemma lem3297050 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297049 _86360 p q r x' h1 h2) (@lem3296123 _86360 q x' h1)). Qed.
Lemma lem3297051 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3297010 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296107 _86360 p x' h1)). Qed.
Lemma lem3297052 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term339 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297051 _86360 p q r x' h1 h2) (@lem3296107 _86360 p x' h1)). Qed.
Lemma lem3297053 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : (term326 _86360 r x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 r x' => @lem3297012 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296091 _86360 r x' h1)). Qed.
Lemma lem3297054 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 r x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297053 _86360 p q r x' h1 h2) (@lem3296091 _86360 r x' h1)). Qed.
Lemma lem3297055 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : (term326 _86360 q x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x' => @lem3297014 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296075 _86360 q x' h1)). Qed.
Lemma lem3297056 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 q x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297055 _86360 p q r x' h1 h2) (@lem3296075 _86360 q x' h1)). Qed.
Lemma lem3297057 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : (term326 _86360 p x') = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x' => @lem3297016 _86360 p q r x' h1 h2) (fun h3 : False => @lem3296059 _86360 p x' h1)). Qed.
Lemma lem3297058 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term326 _86360 p x') (h2 : term342 _86360 p q r x') : False.
Proof. exact (EQ_MP (@lem3297057 _86360 p q r x' h1 h2) (@lem3296059 _86360 p x' h1)). Qed.
Lemma lem3297059 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : (term326 _86360 q x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x => @lem3297018 _86360 q p x h1 h2) (fun h3 : False => @lem3296043 _86360 q x h1)). Qed.
Lemma lem3297060 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297059 _86360 q p x h1 h2) (@lem3296043 _86360 q x h1)). Qed.
Lemma lem3297061 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : (term326 _86360 p x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x => @lem3297020 _86360 q p x h1 h2) (fun h3 : False => @lem3296031 _86360 p x h1)). Qed.
Lemma lem3297062 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term295 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297061 _86360 q p x h1 h2) (@lem3296031 _86360 p x h1)). Qed.
Lemma lem3297063 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : (term326 _86360 p x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 p x => @lem3297022 _86360 q p x h1 h2) (fun h3 : False => @lem3296019 _86360 p x h1)). Qed.
Lemma lem3297064 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 p x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297063 _86360 q p x h1 h2) (@lem3296019 _86360 p x h1)). Qed.
Lemma lem3297065 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : (term326 _86360 q x) = False.
Proof. exact (prop_ext (fun h3 : term326 _86360 q x => @lem3297024 _86360 q p x h1 h2) (fun h3 : False => @lem3296007 _86360 q x h1)). Qed.
Lemma lem3297066 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term326 _86360 q x) (h2 : term297 _86360 q p x) : False.
Proof. exact (EQ_MP (@lem3297065 _86360 q p x h1 h2) (@lem3296007 _86360 q x h1)). Qed.
Lemma lem3297067 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') (h2 : term291 _86360 p q x') : False.
Proof. exact (or_elim (@lem3295993 _86360 p q x' h2) (fun h0 : term326 _86360 p x' => @lem3297028 _86360 p q x' h0 h1) (fun h0 : term326 _86360 q x' => @lem3297026 _86360 p q x' h0 h1)). Qed.
Lemma lem3297068 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term416 _86360 p q x') : False.
Proof. exact (or_elim (@lem3295989 _86360 p q x' h1) (fun h0 : term326 _86360 p x' => @lem3297030 _86360 p q x' h0 h1) (fun h0 : term291 _86360 p q x' => @lem3297067 _86360 p q x' h1 h0)). Qed.
Lemma lem3297069 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term419 _86360 p q x') : False.
Proof. exact (or_elim (@lem3295980 _86360 p q x' h1) (fun h0 : term326 _86360 p x' => @lem3297034 _86360 p q x' h0 h1) (fun h0 : term326 _86360 q x' => @lem3297032 _86360 p q x' h0 h1)). Qed.
Lemma lem3297070 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term423 _86360 p q x') : False.
Proof. exact (or_elim (@lem3295955 _86360 p q x' h1) (fun h0 : term419 _86360 p q x' => @lem3297069 _86360 p q x' h0) (fun h0 : term416 _86360 p q x' => @lem3297068 _86360 p q x' h0)). Qed.
Lemma lem3297071 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') (h2 : term291 _86360 q r x') : False.
Proof. exact (or_elim (@lem3295975 _86360 q r x' h2) (fun h0 : term326 _86360 q x' => @lem3297038 _86360 q p r x' h0 h1) (fun h0 : term326 _86360 r x' => @lem3297036 _86360 q p r x' h0 h1)). Qed.
Lemma lem3297072 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term376 _86360 q p r x') : False.
Proof. exact (or_elim (@lem3295969 _86360 q p r x' h1) (fun h0 : term326 _86360 p x' => @lem3297040 _86360 q p r x' h0 h1) (fun h0 : term291 _86360 q r x' => @lem3297071 _86360 p q r x' h1 h0)). Qed.
Lemma lem3297073 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') (h2 : term291 _86360 p r x') : False.
Proof. exact (or_elim (@lem3295965 _86360 p r x' h2) (fun h0 : term326 _86360 p x' => @lem3297044 _86360 q p r x' h0 h1) (fun h0 : term326 _86360 r x' => @lem3297042 _86360 q p r x' h0 h1)). Qed.
Lemma lem3297074 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term379 _86360 q p r x') : False.
Proof. exact (or_elim (@lem3295958 _86360 q p r x' h1) (fun h0 : term326 _86360 q x' => @lem3297046 _86360 q p r x' h0 h1) (fun h0 : term291 _86360 p r x' => @lem3297073 _86360 q p r x' h1 h0)). Qed.
Lemma lem3297075 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term383 _86360 q p r x') : False.
Proof. exact (or_elim (@lem3295954 _86360 q p r x' h1) (fun h0 : term379 _86360 q p r x' => @lem3297074 _86360 q p r x' h0) (fun h0 : term376 _86360 q p r x' => @lem3297072 _86360 q p r x' h0)). Qed.
Lemma lem3297076 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term865 _86360 r p q x') : False.
Proof. exact (or_elim (@lem3295931 _86360 r p q x' h1) (fun h0 : term383 _86360 q p r x' => @lem3297075 _86360 q p r x' h0) (fun h0 : term423 _86360 p q x' => @lem3297070 _86360 p q x' h0)). Qed.
Lemma lem3297077 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') (h2 : term291 _86360 p q x') : False.
Proof. exact (or_elim (@lem3295950 _86360 p q x' h2) (fun h0 : term326 _86360 p x' => @lem3297052 _86360 p q r x' h0 h1) (fun h0 : term326 _86360 q x' => @lem3297050 _86360 p q r x' h0 h1)). Qed.
Lemma lem3297078 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term339 _86360 p q r x') : False.
Proof. exact (or_elim (@lem3295945 _86360 p q r x' h1) (fun h0 : term291 _86360 p q x' => @lem3297077 _86360 r p q x' h1 h0) (fun h0 : term326 _86360 r x' => @lem3297048 _86360 p q r x' h0 h1)). Qed.
Lemma lem3297079 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') (h2 : term291 _86360 q r x') : False.
Proof. exact (or_elim (@lem3295941 _86360 q r x' h2) (fun h0 : term326 _86360 q x' => @lem3297056 _86360 p q r x' h0 h1) (fun h0 : term326 _86360 r x' => @lem3297054 _86360 p q r x' h0 h1)). Qed.
Lemma lem3297080 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term342 _86360 p q r x') : False.
Proof. exact (or_elim (@lem3295934 _86360 p q r x' h1) (fun h0 : term326 _86360 p x' => @lem3297058 _86360 p q r x' h0 h1) (fun h0 : term291 _86360 q r x' => @lem3297079 _86360 p q r x' h1 h0)). Qed.
Lemma lem3297081 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) (x' : _86360) (h1 : term346 _86360 p q r x') : False.
Proof. exact (or_elim (@lem3295930 _86360 p q r x' h1) (fun h0 : term342 _86360 p q r x' => @lem3297080 _86360 p q r x' h0) (fun h0 : term339 _86360 p q r x' => @lem3297078 _86360 p q r x' h0)). Qed.
Lemma lem3297082 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term944 _86360 r p q x') : False.
Proof. exact (or_elim (@lem3295915 _86360 r p q x' h1) (fun h0 : term346 _86360 p q r x' => @lem3297081 _86360 p q r x' h0) (fun h0 : term865 _86360 r p q x' => @lem3297076 _86360 r p q x' h0)). Qed.
Lemma lem3297083 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term295 _86360 q p x) : False.
Proof. exact (or_elim (@lem3295925 _86360 q p x h1) (fun h0 : term326 _86360 p x => @lem3297062 _86360 q p x h0 h1) (fun h0 : term326 _86360 q x => @lem3297060 _86360 q p x h0 h1)). Qed.
Lemma lem3297084 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term297 _86360 q p x) : False.
Proof. exact (or_elim (@lem3295918 _86360 q p x h1) (fun h0 : term326 _86360 q x => @lem3297066 _86360 q p x h0 h1) (fun h0 : term326 _86360 p x => @lem3297064 _86360 q p x h0 h1)). Qed.
Lemma lem3297085 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) (x : _86360) (h1 : term301 _86360 q p x) : False.
Proof. exact (or_elim (@lem3295914 _86360 q p x h1) (fun h0 : term297 _86360 q p x => @lem3297084 _86360 q p x h0) (fun h0 : term295 _86360 q p x => @lem3297083 _86360 q p x h0)). Qed.
Lemma lem3297086 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term1030 _86360 x r p q x') : False.
Proof. exact (or_elim (@lem3295913 _86360 x r p q x' h1) (fun h0 : term301 _86360 q p x => @lem3297085 _86360 q p x h0) (fun h0 : term944 _86360 r p q x' => @lem3297082 _86360 r p q x' h0)). Qed.
Lemma lem3297087 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term1030 _86360 x r p q x') : (term1030 _86360 x r p q x') = False.
Proof. exact (prop_ext (fun h2 : term1030 _86360 x r p q x' => @lem3297086 _86360 x r p q x' h1) (fun h2 : False => @lem3295913 _86360 x r p q x' h1)). Qed.
Lemma lem3297088 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (x' : _86360) (h1 : term1030 _86360 x r p q x') : False.
Proof. exact (EQ_MP (@lem3297087 _86360 x r p q x' h1) (@lem3295913 _86360 x r p q x' h1)). Qed.
Lemma lem3297089 {_86360 : Type'} (x : _86360) (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term1033 _86360 x r p q) : False.
Proof. exact (ex_elim (@lem3295620 _86360 x r p q h1) (fun x' : _86360 => fun h0 : term1032 _86360 x r p q x' => @lem3297088 _86360 x r p q x' h0)). Qed.
Lemma lem3297090 {_86360 : Type'} (x : _86360) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term1035 _86360 x p q) : False.
Proof. exact (ex_elim (@lem3295619 _86360 x p q h1) (fun r : _86360 -> Prop => fun h0 : term1034 _86360 x p q r => @lem3297089 _86360 x r p q h0)). Qed.
Lemma lem3297091 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term1037 _86360 p q) : False.
Proof. exact (ex_elim (@lem3295618 _86360 p q h1) (fun x : _86360 => fun h0 : term1036 _86360 p q x => @lem3297090 _86360 x p q h0)). Qed.
Lemma lem3297092 {_86360 : Type'} (q : _86360 -> Prop) (h1 : term1039 _86360 q) : False.
Proof. exact (ex_elim (@lem3295617 _86360 q h1) (fun p : _86360 -> Prop => fun h0 : term1038 _86360 q p => @lem3297091 _86360 p q h0)). Qed.
Lemma lem3297093 {_86360 : Type'} (h1 : term289 _86360) : False.
Proof. exact (ex_elim (@lem3295616 _86360 h1) (fun q : _86360 -> Prop => fun h0 : term1040 _86360 q => @lem3297092 _86360 q h0)). Qed.
Lemma lem3297094 {_86360 : Type'} (h1 : term289 _86360) : (term289 _86360) = False.
Proof. exact (prop_ext (fun h2 : term289 _86360 => @lem3297093 _86360 h1) (fun h2 : False => @lem3292508 _86360 h1)). Qed.
Lemma lem3297095 {_86360 : Type'} (h1 : term289 _86360) : False.
Proof. exact (EQ_MP (@lem3297094 _86360 h1) (@lem3292508 _86360 h1)). Qed.
Lemma lem3297096 {_86360 : Type'} : term288 _86360.
Proof. exact (fun h0 : term289 _86360 => @lem3297095 _86360 h0). Qed.
Lemma lem3297097 {_86360 : Type'} : term287 _86360.
Proof. exact (EQ_MP (@lem3292507 _86360) (@lem3297096 _86360)). Qed.
Lemma lem3297098 {_86360 : Type'} : term224 _86360.
Proof. exact (EQ_MP (@lem3292503 _86360) (@lem3297097 _86360)). Qed.
Lemma lem3297099 {_86360 : Type'} (q : _86360 -> Prop) : term1046 _86360 q.
Proof. exact (@lem3297098 _86360 q). Qed.
Lemma lem3297100 {_86360 : Type'} (q : _86360 -> Prop) : (term1046 _86360 q) = (term158 _86360 q).
Proof. exact (eq_refl (term1046 _86360 q)). Qed.
Lemma lem3297101 {_86360 : Type'} (q : _86360 -> Prop) : term158 _86360 q.
Proof. exact (EQ_MP (@lem3297100 _86360 q) (@lem3297099 _86360 q)). Qed.
Lemma lem3297102 {_86360 : Type'} (q : _86360 -> Prop) (p : _86360 -> Prop) : term1047 _86360 q p.
Proof. exact (@lem3297101 _86360 q p). Qed.
Lemma lem3297103 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1047 _86360 q p) = (term86 _86360 p q).
Proof. exact (eq_refl (term1047 _86360 q p)). Qed.
Lemma lem3297104 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) : term86 _86360 p q.
Proof. exact (EQ_MP (@lem3297103 _86360 p q) (@lem3297102 _86360 q p)). Qed.
Lemma lem3297105 {_86360 : Type'} (p : _86360 -> Prop) (q : _86360 -> Prop) (r : _86360 -> Prop) : term1048 _86360 p q r.
Proof. exact (@lem3297104 _86360 p q r). Qed.
Lemma lem3297106 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : (term1048 _86360 p q r) = (term77 _86360 r p q).
Proof. exact (eq_refl (term1048 _86360 p q r)). Qed.
Lemma lem3297107 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term77 _86360 r p q.
Proof. exact (EQ_MP (@lem3297106 _86360 r p q) (@lem3297105 _86360 p q r)). Qed.
Lemma lem3297109 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term77 _86360 r p q.
Proof. exact (@lem3291674 _86360 r p q (@lem3297107 _86360 r p q)). Qed.
Lemma lem3297110 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term78 _86360 r p q) : False.
Proof. exact (@lem3297109 _86360 r p q (@lem3291658 _86360 r p q h1)). Qed.
Lemma lem3297111 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term78 _86360 r p q) : (term78 _86360 r p q) = False.
Proof. exact (prop_ext (fun h2 : term78 _86360 r p q => @lem3297110 _86360 r p q h1) (fun h2 : False => @lem3291658 _86360 r p q h1)). Qed.
Lemma lem3297112 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) (h1 : term78 _86360 r p q) : False.
Proof. exact (EQ_MP (@lem3297111 _86360 r p q h1) (@lem3291658 _86360 r p q h1)). Qed.
Lemma lem3297113 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term77 _86360 r p q.
Proof. exact (fun h0 : term78 _86360 r p q => @lem3297112 _86360 r p q h0). Qed.
Lemma lem3297114 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term75 _86360 r p q.
Proof. exact (EQ_MP (@lem3291657 _86360 r p q) (@lem3297113 _86360 r p q)). Qed.
Lemma lem3297115 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term24 _86360 r p q.
Proof. exact (EQ_MP (@lem3291653 _86360 r p q) (@lem3297114 _86360 r p q)). Qed.
Lemma lem3297116 {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop) : term23 _86360 r p q.
Proof. exact (EQ_MP (@lem3291259 _86360 r p q) (@lem3297115 _86360 r p q)). Qed.
