Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_OVER_INTER_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3261116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3261117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3261116 A s t). Qed.
Lemma lem3261118 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : ((term1 A s t u) = (term2 A t s u)) = (term3 A t s u).
Proof. exact (@lem3261117 A (term1 A s t u) (term2 A t s u)). Qed.
Lemma lem3261127 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term4 A t s) = (term5 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3261118 A t s u)). Qed.
Lemma lem3261128 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261129 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A t s) = (term7 A t s).
Proof. exact (MK_COMB (@lem3261128 A) (@lem3261127 A t s)). Qed.
Lemma lem3261134 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3261129 A t s)). Qed.
Lemma lem3261135 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261136 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3261135 A) (@lem3261134 A s)). Qed.
Lemma lem3261141 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3261136 A s)). Qed.
Lemma lem3261142 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261143 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3261142 A) (@lem3261141 A)). Qed.
Lemma lem3261148 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3261143 A)). Qed.
Lemma lem3261168 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3261169 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3261168 A s x t). Qed.
Lemma lem3261170 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term18 A x s t u) = (term19 A s x t u).
Proof. exact (@lem3261169 A s x (@UNION A t u)). Qed.
Lemma lem3261174 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261175 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261174 A P x). Qed.
Lemma lem3261176 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3261175 A s x). Qed.
Lemma lem3261177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3261178 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3261177) (@lem3261176 A s x)). Qed.
Lemma lem3261180 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3261181 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (@lem3261180 A s x t). Qed.
Lemma lem3261182 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term22 A x t u) = (term23 A t x u).
Proof. exact (@lem3261181 A t x u). Qed.
Lemma lem3261186 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261187 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261186 A P x). Qed.
Lemma lem3261188 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3261187 A t x). Qed.
Lemma lem3261189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3261190 {A : Type'} (t : A -> Prop) (x : A) : (term24 A x t) = (term25 A t x).
Proof. exact (MK_COMB (@lem3261189) (@lem3261188 A t x)). Qed.
Lemma lem3261192 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261193 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261192 A P x). Qed.
Lemma lem3261194 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3261193 A u x). Qed.
Lemma lem3261195 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term23 A t x u) = (term26 A t u x).
Proof. exact (MK_COMB (@lem3261190 A t x) (@lem3261194 A u x)). Qed.
Lemma lem3261198 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term22 A x t u) = (term26 A t u x).
Proof. exact (TRANS (@lem3261182 A t x u) (@lem3261195 A t u x)). Qed.
Lemma lem3261199 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term19 A s x t u) = (term27 A s t u x).
Proof. exact (MK_COMB (@lem3261178 A s x) (@lem3261198 A t u x)). Qed.
Lemma lem3261202 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term18 A x s t u) = (term27 A s t u x).
Proof. exact (TRANS (@lem3261170 A s x t u) (@lem3261199 A s t u x)). Qed.
Lemma lem3261203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3261204 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term28 A x s t u) = (term29 A s t u x).
Proof. exact (MK_COMB (@lem3261203) (@lem3261202 A s t u x)). Qed.
Lemma lem3261206 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3261207 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (@lem3261206 A s x t). Qed.
Lemma lem3261208 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) : (term30 A x t s u) = (term31 A t x s u).
Proof. exact (@lem3261207 A (@INTER A s t) x (@INTER A s u)). Qed.
Lemma lem3261212 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3261213 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3261212 A s x t). Qed.
Lemma lem3261217 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261218 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261217 A P x). Qed.
Lemma lem3261219 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3261218 A s x). Qed.
Lemma lem3261220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3261221 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3261220) (@lem3261219 A s x)). Qed.
Lemma lem3261223 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261224 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261223 A P x). Qed.
Lemma lem3261225 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3261224 A t x). Qed.
Lemma lem3261226 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s x t) = (term32 A s t x).
Proof. exact (MK_COMB (@lem3261221 A s x) (@lem3261225 A t x)). Qed.
Lemma lem3261229 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A x s t) = (term32 A s t x).
Proof. exact (TRANS (@lem3261213 A s x t) (@lem3261226 A s t x)). Qed.
Lemma lem3261230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3261231 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term33 A x s t) = (term34 A s t x).
Proof. exact (MK_COMB (@lem3261230) (@lem3261229 A s t x)). Qed.
Lemma lem3261233 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3261234 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3261233 A s x t). Qed.
Lemma lem3261235 {A : Type'} (s : A -> Prop) (x : A) (u : A -> Prop) : (term16 A x s u) = (term17 A s x u).
Proof. exact (@lem3261234 A s x u). Qed.
Lemma lem3261239 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261240 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261239 A P x). Qed.
Lemma lem3261241 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3261240 A s x). Qed.
Lemma lem3261242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3261243 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3261242) (@lem3261241 A s x)). Qed.
Lemma lem3261245 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3261246 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3261245 A P x). Qed.
Lemma lem3261247 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3261246 A u x). Qed.
Lemma lem3261248 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term17 A s x u) = (term32 A s u x).
Proof. exact (MK_COMB (@lem3261243 A s x) (@lem3261247 A u x)). Qed.
Lemma lem3261251 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term16 A x s u) = (term32 A s u x).
Proof. exact (TRANS (@lem3261235 A s x u) (@lem3261248 A s u x)). Qed.
Lemma lem3261252 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term31 A t x s u) = (term35 A t s u x).
Proof. exact (MK_COMB (@lem3261231 A s t x) (@lem3261251 A s u x)). Qed.
Lemma lem3261255 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term30 A x t s u) = (term35 A t s u x).
Proof. exact (TRANS (@lem3261208 A t x s u) (@lem3261252 A t s u x)). Qed.
Lemma lem3261256 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : ((term18 A x s t u) = (term30 A x t s u)) = ((term27 A s t u x) = (term35 A t s u x)).
Proof. exact (MK_COMB (@lem3261204 A s t u x) (@lem3261255 A t s u x)). Qed.
Lemma lem3261259 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term36 A t s u) = (term37 A t s u).
Proof. exact (fun_ext (fun x : A => @lem3261256 A t s u x)). Qed.
Lemma lem3261260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3261261 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term3 A t s u) = (term38 A t s u).
Proof. exact (MK_COMB (@lem3261260 A) (@lem3261259 A t s u)). Qed.
Lemma lem3261266 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A t s) = (term39 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3261261 A t s u)). Qed.
Lemma lem3261267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261268 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term7 A t s) = (term40 A t s).
Proof. exact (MK_COMB (@lem3261267 A) (@lem3261266 A t s)). Qed.
Lemma lem3261273 {A : Type'} (s : A -> Prop) : (term9 A s) = (term41 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3261268 A t s)). Qed.
Lemma lem3261274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261275 {A : Type'} (s : A -> Prop) : (term11 A s) = (term42 A s).
Proof. exact (MK_COMB (@lem3261274 A) (@lem3261273 A s)). Qed.
Lemma lem3261280 {A : Type'} : (term13 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3261275 A s)). Qed.
Lemma lem3261281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261282 {A : Type'} : (term15 A) = (term44 A).
Proof. exact (MK_COMB (@lem3261281 A) (@lem3261280 A)). Qed.
Lemma lem3261287 {A : Type'} : (term44 A) = (term15 A).
Proof. exact (SYM (@lem3261282 A)). Qed.
Lemma lem3261289 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3261290 {A : Type'} : (term44 A) = (term46 A).
Proof. exact (@lem3261289 (term44 A)). Qed.
Lemma lem3261291 {A : Type'} : (term46 A) = (term44 A).
Proof. exact (SYM (@lem3261290 A)). Qed.
Lemma lem3261292 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem3261295 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem3261296 {A : Type'} : term48 A.
Proof. exact (fun h0 : term46 A => @lem3261295 A h0). Qed.
Lemma lem3261297 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3261298 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem3261299 {A : Type'} (h1 : term46 A) (h2 : term48 A) : term46 A.
Proof. exact (@lem3261297 A h2 (@lem3261298 A h1)). Qed.
Lemma lem3261300 {A : Type'} (h1 : term46 A) : term49 A.
Proof. exact (fun h0 : term48 A => @lem3261299 A h1 h0). Qed.
Lemma lem3261301 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3261302 {A : Type'} (h1 : term46 A) (h2 : term48 A) : term46 A.
Proof. exact (@lem3261300 A h1 (@lem3261301 A h2)). Qed.
Lemma lem3261303 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (fun h0 : term46 A => @lem3261302 A h0 h1). Qed.
Lemma lem3261304 {A : Type'} : term50 A.
Proof. exact (fun h0 : term48 A => @lem3261303 A h0). Qed.
Lemma lem3261307 {A : Type'} : term48 A.
Proof. exact (@lem3261304 A (@lem3261296 A)). Qed.
Lemma lem3261308 {A : Type'} : term48 A.
Proof. exact (@lem3261307 A). Qed.
Lemma lem3261310 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3261311 {A : Type'} : (term46 A) = (term51 A).
Proof. exact (@lem3261310 (term47 A)). Qed.
Lemma lem3261313 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3261314 {A : Type'} : (term51 A) = (term44 A).
Proof. exact (@lem3261313 (term44 A)). Qed.
Lemma lem3261345 {A : Type'} : (term46 A) = (term44 A).
Proof. exact (TRANS (@lem3261311 A) (@lem3261314 A)). Qed.
Lemma lem3261370 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : ((term27 A s t u x) = (term35 A t s u x)) = ((term27 A s t u x) = (term35 A t s u x)).
Proof. exact (eq_refl ((term27 A s t u x) = (term35 A t s u x))). Qed.
Lemma lem3261371 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term37 A t s u) = (term37 A t s u).
Proof. exact (fun_ext (fun x : A => @lem3261370 A t s u x)). Qed.
Lemma lem3261372 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3261373 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term38 A t s u) = (term38 A t s u).
Proof. exact (MK_COMB (@lem3261372 A) (@lem3261371 A t s u)). Qed.
Lemma lem3261374 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A t s) = (term39 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3261373 A t s u)). Qed.
Lemma lem3261375 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261376 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term40 A t s) = (term40 A t s).
Proof. exact (MK_COMB (@lem3261375 A) (@lem3261374 A t s)). Qed.
Lemma lem3261377 {A : Type'} (s : A -> Prop) : (term41 A s) = (term41 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3261376 A t s)). Qed.
Lemma lem3261378 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261379 {A : Type'} (s : A -> Prop) : (term42 A s) = (term42 A s).
Proof. exact (MK_COMB (@lem3261378 A) (@lem3261377 A s)). Qed.
Lemma lem3261380 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3261379 A s)). Qed.
Lemma lem3261381 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3261382 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (MK_COMB (@lem3261381 A) (@lem3261380 A)). Qed.
Lemma lem3261419 {A : Type'} : (term46 A) = (term44 A).
Proof. exact (TRANS (@lem3261345 A) (@lem3261382 A)). Qed.
Lemma lem3261420 {A : Type'} : (term44 A) = (term46 A).
Proof. exact (SYM (@lem3261419 A)). Qed.
Lemma lem3261422 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3261423 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : ((term27 A s t u x) = (term35 A t s u x)) = (term53 A t s u x).
Proof. exact (@lem3261422 ((term27 A s t u x) = (term35 A t s u x))). Qed.
Lemma lem3261424 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term53 A t s u x) = ((term27 A s t u x) = (term35 A t s u x)).
Proof. exact (SYM (@lem3261423 A t s u x)). Qed.
Lemma lem3261425 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : term54 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3261436 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term55 A t u x) = (term56 A t u x).
Proof. exact (@lem17160 (t x) (u x)). Qed.
Lemma lem3261441 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (term57 A s x).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem3261442 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term58 A s t u x) = (term59 A s t u x).
Proof. exact (MK_COMB (@lem3261441 A s x) (@lem3261436 A t u x)). Qed.
Lemma lem3261443 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A s t u x) = (term58 A s t u x).
Proof. exact (@lem17045 (s x) (term26 A t u x)). Qed.
Lemma lem3261444 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A s t u x) = (term59 A s t u x).
Proof. exact (TRANS (@lem3261443 A s t u x) (@lem3261442 A s t u x)). Qed.
Lemma lem3261456 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term61 A s t x) = (term62 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3261468 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term61 A s u x) = (term62 A s u x).
Proof. exact (@lem17045 (s x) (u x)). Qed.
Lemma lem3261472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3261473 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term64 A s t x).
Proof. exact (MK_COMB (@lem3261472) (@lem3261456 A s t x)). Qed.
Lemma lem3261474 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term65 A t s u x) = (term66 A t s u x).
Proof. exact (MK_COMB (@lem3261473 A s t x) (@lem3261468 A s u x)). Qed.
Lemma lem3261475 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term67 A t s u x) = (term65 A t s u x).
Proof. exact (@lem17160 (term32 A s t x) (term32 A s u x)). Qed.
Lemma lem3261476 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term67 A t s u x) = (term66 A t s u x).
Proof. exact (TRANS (@lem3261475 A t s u x) (@lem3261474 A t s u x)). Qed.
Lemma lem3261479 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term35 A t s u x) = (term35 A t s u x).
Proof. exact (eq_refl (term35 A t s u x)). Qed.
Lemma lem3261480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3261481 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term68 A s t u x) = (term69 A s t u x).
Proof. exact (MK_COMB (@lem3261480) (@lem3261444 A s t u x)). Qed.
Lemma lem3261482 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term70 A t s u x) = (term71 A t s u x).
Proof. exact (MK_COMB (@lem3261481 A s t u x) (@lem3261479 A t s u x)). Qed.
Lemma lem3261484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term72 A s t u x) = (term72 A s t u x).
Proof. exact (eq_refl (term72 A s t u x)). Qed.
Lemma lem3261485 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term73 A t s u x) = (term74 A t s u x).
Proof. exact (MK_COMB (@lem3261484 A s t u x) (@lem3261476 A t s u x)). Qed.
Lemma lem3261486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3261487 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term75 A t s u x) = (term76 A t s u x).
Proof. exact (MK_COMB (@lem3261486) (@lem3261485 A t s u x)). Qed.
Lemma lem3261488 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term77 A t s u x) = (term78 A t s u x).
Proof. exact (MK_COMB (@lem3261487 A t s u x) (@lem3261482 A t s u x)). Qed.
Lemma lem3261489 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term54 A t s u x) = (term77 A t s u x).
Proof. exact (@lem17646 (term27 A s t u x) (term35 A t s u x)). Qed.
Lemma lem3261494 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term54 A t s u x) = (term78 A t s u x).
Proof. exact (TRANS (@lem3261489 A t s u x) (@lem3261488 A t s u x)). Qed.
Lemma lem3261591 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : term78 A t s u x.
Proof. exact (EQ_MP (@lem3261494 A t s u x) (@lem3261425 A t s u x h1)). Qed.
Lemma lem3261592 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term74 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3261593 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term71 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3261594 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term66 A t s u x.
Proof. exact (proj2 (@lem3261592 A t s u x h1)). Qed.
Lemma lem3261595 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term27 A s t u x.
Proof. exact (proj1 (@lem3261592 A t s u x h1)). Qed.
Lemma lem3261596 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term62 A s u x.
Proof. exact (proj2 (@lem3261594 A t s u x h1)). Qed.
Lemma lem3261597 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term62 A s t x.
Proof. exact (proj1 (@lem3261594 A t s u x h1)). Qed.
Lemma lem3261598 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term26 A t u x.
Proof. exact (proj2 (@lem3261595 A t s u x h1)). Qed.
Lemma lem3261614 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term35 A t s u x.
Proof. exact (proj2 (@lem3261593 A t s u x h1)). Qed.
Lemma lem3261615 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term59 A s t u x.
Proof. exact (proj1 (@lem3261593 A t s u x h1)). Qed.
Lemma lem3261616 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : term32 A s t x.
Proof. exact (h1). Qed.
Lemma lem3261617 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : term32 A s u x.
Proof. exact (h1). Qed.
Lemma lem3261621 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) : term56 A t u x.
Proof. exact (h1). Qed.
Lemma lem3261627 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) : term56 A t u x.
Proof. exact (h1). Qed.
Lemma lem3261641 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261645 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261653 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3261661 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3261677 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261685 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3261693 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3261705 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261709 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261721 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261741 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261749 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3261753 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term79 A u x.
Proof. exact (h1). Qed.
Lemma lem3261769 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261797 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261819 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261821 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261825 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3261829 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3261837 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261841 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3261845 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3261851 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261853 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261859 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261869 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261873 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3261875 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term79 A u x.
Proof. exact (h1). Qed.
Lemma lem3261883 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261889 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) : term79 A t x.
Proof. exact (proj1 (@lem3261621 A t u x h1)). Qed.
Lemma lem3261897 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term79 A s x.
Proof. exact (h1). Qed.
Lemma lem3261905 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) : term79 A u x.
Proof. exact (proj2 (@lem3261627 A t u x h1)). Qed.
Lemma lem3261907 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (proj1 (@lem3261595 A t s u x h1)). Qed.
Lemma lem3261908 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3261907 A t s u x h1). Qed.
Lemma lem3261910 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261911 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3261910 (s x)). Qed.
Lemma lem3261912 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (EQ_MP (@lem3261911 A s x) (@lem3261908 A t s u x h1)). Qed.
Lemma lem3261915 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3261917 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3261915 (s x)). Qed.
Lemma lem3261920 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3261917 A s x) (@lem3261819 A s x h1)). Qed.
Lemma lem3261923 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (@lem3261920 A s x h1 (@lem3261912 A t s u x h2)). Qed.
Lemma lem3261924 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3261923 A t s u x h1 h2). Qed.
Lemma lem3261926 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261927 : term83 = False.
Proof. exact (@lem3261926 False). Qed.
Lemma lem3261928 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3261927) (@lem3261924 A t s u x h1 h2)). Qed.
Lemma lem3261930 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3261931 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term80 A t x.
Proof. exact (fun h0 : term79 A t x => @lem3261930 A t x h1). Qed.
Lemma lem3261933 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261934 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (t x).
Proof. exact (@lem3261933 (t x)). Qed.
Lemma lem3261935 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3261934 A t x) (@lem3261931 A t x h1)). Qed.
Lemma lem3261938 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3261940 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term82 A t x).
Proof. exact (@lem3261938 (t x)). Qed.
Lemma lem3261943 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term82 A t x.
Proof. exact (EQ_MP (@lem3261940 A t x) (@lem3261829 A t x h1)). Qed.
Lemma lem3261946 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (@lem3261943 A t x h1 (@lem3261935 A t x h2)). Qed.
Lemma lem3261947 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3261946 A t x h1 h2). Qed.
Lemma lem3261949 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261950 : term83 = False.
Proof. exact (@lem3261949 False). Qed.
Lemma lem3261951 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3261950) (@lem3261947 A t x h1 h2)). Qed.
Lemma lem3261953 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (proj1 (@lem3261595 A t s u x h1)). Qed.
Lemma lem3261954 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3261953 A t s u x h1). Qed.
Lemma lem3261956 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261957 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3261956 (s x)). Qed.
Lemma lem3261958 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (EQ_MP (@lem3261957 A s x) (@lem3261954 A t s u x h1)). Qed.
Lemma lem3261961 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3261963 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3261961 (s x)). Qed.
Lemma lem3261966 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3261963 A s x) (@lem3261837 A s x h1)). Qed.
Lemma lem3261969 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (@lem3261966 A s x h1 (@lem3261958 A t s u x h2)). Qed.
Lemma lem3261970 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3261969 A t s u x h1 h2). Qed.
Lemma lem3261972 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261973 : term83 = False.
Proof. exact (@lem3261972 False). Qed.
Lemma lem3261974 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3261973) (@lem3261970 A t s u x h1 h2)). Qed.
Lemma lem3261976 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3261977 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term80 A t x.
Proof. exact (fun h0 : term79 A t x => @lem3261976 A t x h1). Qed.
Lemma lem3261979 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261980 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (t x).
Proof. exact (@lem3261979 (t x)). Qed.
Lemma lem3261981 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3261980 A t x) (@lem3261977 A t x h1)). Qed.
Lemma lem3261984 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3261986 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term82 A t x).
Proof. exact (@lem3261984 (t x)). Qed.
Lemma lem3261989 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term82 A t x.
Proof. exact (EQ_MP (@lem3261986 A t x) (@lem3261845 A t x h1)). Qed.
Lemma lem3261992 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (@lem3261989 A t x h1 (@lem3261981 A t x h2)). Qed.
Lemma lem3261993 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3261992 A t x h1 h2). Qed.
Lemma lem3261995 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3261996 : term83 = False.
Proof. exact (@lem3261995 False). Qed.
Lemma lem3261997 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3261996) (@lem3261993 A t x h1 h2)). Qed.
Lemma lem3261999 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (proj1 (@lem3261595 A t s u x h1)). Qed.
Lemma lem3262000 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3261999 A t s u x h1). Qed.
Lemma lem3262002 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262003 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3262002 (s x)). Qed.
Lemma lem3262004 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (EQ_MP (@lem3262003 A s x) (@lem3262000 A t s u x h1)). Qed.
Lemma lem3262007 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262009 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3262007 (s x)). Qed.
Lemma lem3262012 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3262009 A s x) (@lem3261851 A s x h1)). Qed.
Lemma lem3262015 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (@lem3262012 A s x h1 (@lem3262004 A t s u x h2)). Qed.
Lemma lem3262016 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262015 A t s u x h1 h2). Qed.
Lemma lem3262018 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262019 : term83 = False.
Proof. exact (@lem3262018 False). Qed.
Lemma lem3262020 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262019) (@lem3262016 A t s u x h1 h2)). Qed.
Lemma lem3262022 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (proj1 (@lem3261595 A t s u x h1)). Qed.
Lemma lem3262023 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3262022 A t s u x h1). Qed.
Lemma lem3262025 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262026 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3262025 (s x)). Qed.
Lemma lem3262027 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (EQ_MP (@lem3262026 A s x) (@lem3262023 A t s u x h1)). Qed.
Lemma lem3262030 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262032 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3262030 (s x)). Qed.
Lemma lem3262035 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3262032 A s x) (@lem3261859 A s x h1)). Qed.
Lemma lem3262038 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (@lem3262035 A s x h1 (@lem3262027 A t s u x h2)). Qed.
Lemma lem3262039 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262038 A t s u x h1 h2). Qed.
Lemma lem3262041 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262042 : term83 = False.
Proof. exact (@lem3262041 False). Qed.
Lemma lem3262043 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262042) (@lem3262039 A t s u x h1 h2)). Qed.
Lemma lem3262045 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (proj1 (@lem3261595 A t s u x h1)). Qed.
Lemma lem3262046 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3262045 A t s u x h1). Qed.
Lemma lem3262048 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262049 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3262048 (s x)). Qed.
Lemma lem3262050 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : s x.
Proof. exact (EQ_MP (@lem3262049 A s x) (@lem3262046 A t s u x h1)). Qed.
Lemma lem3262053 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262055 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3262053 (s x)). Qed.
Lemma lem3262058 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3262055 A s x) (@lem3261869 A s x h1)). Qed.
Lemma lem3262061 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (@lem3262058 A s x h1 (@lem3262050 A t s u x h2)). Qed.
Lemma lem3262062 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262061 A t s u x h1 h2). Qed.
Lemma lem3262064 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262065 : term83 = False.
Proof. exact (@lem3262064 False). Qed.
Lemma lem3262066 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262065) (@lem3262062 A t s u x h1 h2)). Qed.
Lemma lem3262068 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3262069 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : term80 A u x.
Proof. exact (fun h0 : term79 A u x => @lem3262068 A u x h1). Qed.
Lemma lem3262071 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262072 {A : Type'} (u : A -> Prop) (x : A) : (term80 A u x) = (u x).
Proof. exact (@lem3262071 (u x)). Qed.
Lemma lem3262073 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem3262072 A u x) (@lem3262069 A u x h1)). Qed.
Lemma lem3262076 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262078 {A : Type'} (u : A -> Prop) (x : A) : (term79 A u x) = (term82 A u x).
Proof. exact (@lem3262076 (u x)). Qed.
Lemma lem3262081 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term82 A u x.
Proof. exact (EQ_MP (@lem3262078 A u x) (@lem3261875 A u x h1)). Qed.
Lemma lem3262084 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (@lem3262081 A u x h1 (@lem3262073 A u x h2)). Qed.
Lemma lem3262085 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262084 A u x h1 h2). Qed.
Lemma lem3262087 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262088 : term83 = False.
Proof. exact (@lem3262087 False). Qed.
Lemma lem3262089 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262088) (@lem3262085 A u x h1 h2)). Qed.
Lemma lem3262091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : s x.
Proof. exact (proj1 (@lem3261616 A s t x h1)). Qed.
Lemma lem3262092 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3262091 A s t x h1). Qed.
Lemma lem3262094 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262095 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3262094 (s x)). Qed.
Lemma lem3262096 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : s x.
Proof. exact (EQ_MP (@lem3262095 A s x) (@lem3262092 A s t x h1)). Qed.
Lemma lem3262099 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262101 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3262099 (s x)). Qed.
Lemma lem3262104 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3262101 A s x) (@lem3261883 A s x h1)). Qed.
Lemma lem3262107 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : False.
Proof. exact (@lem3262104 A s x h1 (@lem3262096 A s t x h2)). Qed.
Lemma lem3262108 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262107 A s t x h1 h2). Qed.
Lemma lem3262110 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262111 : term83 = False.
Proof. exact (@lem3262110 False). Qed.
Lemma lem3262112 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : False.
Proof. exact (EQ_MP (@lem3262111) (@lem3262108 A s t x h1 h2)). Qed.
Lemma lem3262114 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : t x.
Proof. exact (proj2 (@lem3261616 A s t x h1)). Qed.
Lemma lem3262115 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : term80 A t x.
Proof. exact (fun h0 : term79 A t x => @lem3262114 A s t x h1). Qed.
Lemma lem3262117 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262118 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (t x).
Proof. exact (@lem3262117 (t x)). Qed.
Lemma lem3262119 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term32 A s t x) : t x.
Proof. exact (EQ_MP (@lem3262118 A t x) (@lem3262115 A s t x h1)). Qed.
Lemma lem3262122 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262124 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term82 A t x).
Proof. exact (@lem3262122 (t x)). Qed.
Lemma lem3262127 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) : term82 A t x.
Proof. exact (EQ_MP (@lem3262124 A t x) (@lem3261889 A t u x h1)). Qed.
Lemma lem3262130 {A : Type'} (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term56 A t u x) (h2 : term32 A s t x) : False.
Proof. exact (@lem3262127 A t u x h1 (@lem3262119 A s t x h2)). Qed.
Lemma lem3262131 {A : Type'} (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term56 A t u x) (h2 : term32 A s t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262130 A u s t x h1 h2). Qed.
Lemma lem3262133 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262134 : term83 = False.
Proof. exact (@lem3262133 False). Qed.
Lemma lem3262135 {A : Type'} (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term56 A t u x) (h2 : term32 A s t x) : False.
Proof. exact (EQ_MP (@lem3262134) (@lem3262131 A u s t x h1 h2)). Qed.
Lemma lem3262137 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : s x.
Proof. exact (proj1 (@lem3261617 A s u x h1)). Qed.
Lemma lem3262138 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3262137 A s u x h1). Qed.
Lemma lem3262140 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262141 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3262140 (s x)). Qed.
Lemma lem3262142 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : s x.
Proof. exact (EQ_MP (@lem3262141 A s x) (@lem3262138 A s u x h1)). Qed.
Lemma lem3262145 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262147 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3262145 (s x)). Qed.
Lemma lem3262150 {A : Type'} (s : A -> Prop) (x : A) (h1 : term79 A s x) : term82 A s x.
Proof. exact (EQ_MP (@lem3262147 A s x) (@lem3261897 A s x h1)). Qed.
Lemma lem3262153 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : False.
Proof. exact (@lem3262150 A s x h1 (@lem3262142 A s u x h2)). Qed.
Lemma lem3262154 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262153 A s u x h1 h2). Qed.
Lemma lem3262156 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262157 : term83 = False.
Proof. exact (@lem3262156 False). Qed.
Lemma lem3262158 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : False.
Proof. exact (EQ_MP (@lem3262157) (@lem3262154 A s u x h1 h2)). Qed.
Lemma lem3262160 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : u x.
Proof. exact (proj2 (@lem3261617 A s u x h1)). Qed.
Lemma lem3262161 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : term80 A u x.
Proof. exact (fun h0 : term79 A u x => @lem3262160 A s u x h1). Qed.
Lemma lem3262163 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262164 {A : Type'} (u : A -> Prop) (x : A) : (term80 A u x) = (u x).
Proof. exact (@lem3262163 (u x)). Qed.
Lemma lem3262165 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) : u x.
Proof. exact (EQ_MP (@lem3262164 A u x) (@lem3262161 A s u x h1)). Qed.
Lemma lem3262168 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3262170 {A : Type'} (u : A -> Prop) (x : A) : (term79 A u x) = (term82 A u x).
Proof. exact (@lem3262168 (u x)). Qed.
Lemma lem3262173 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) : term82 A u x.
Proof. exact (EQ_MP (@lem3262170 A u x) (@lem3261905 A t u x h1)). Qed.
Lemma lem3262176 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) (h2 : term32 A s u x) : False.
Proof. exact (@lem3262173 A t u x h1 (@lem3262165 A s u x h2)). Qed.
Lemma lem3262177 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) (h2 : term32 A s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3262176 A t s u x h1 h2). Qed.
Lemma lem3262179 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3262180 : term83 = False.
Proof. exact (@lem3262179 False). Qed.
Lemma lem3262181 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term56 A t u x) (h2 : term32 A s u x) : False.
Proof. exact (EQ_MP (@lem3262180) (@lem3262177 A t s u x h1 h2)). Qed.
Lemma lem3262182 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262158 A s u x h1 h2) (fun h3 : False => @lem3261897 A s x h1)). Qed.
Lemma lem3262183 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : False.
Proof. exact (EQ_MP (@lem3262182 A s u x h1 h2) (@lem3261897 A s x h1)). Qed.
Lemma lem3262184 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262112 A s t x h1 h2) (fun h3 : False => @lem3261883 A s x h1)). Qed.
Lemma lem3262185 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : False.
Proof. exact (EQ_MP (@lem3262184 A s t x h1 h2) (@lem3261883 A s x h1)). Qed.
Lemma lem3262186 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3262089 A u x h1 h2) (fun h3 : False => @lem3261875 A u x h1)). Qed.
Lemma lem3262187 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262186 A u x h1 h2) (@lem3261875 A u x h1)). Qed.
Lemma lem3262188 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3262187 A u x h1 h2) (fun h3 : False => @lem3261873 A u x h2)). Qed.
Lemma lem3262189 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262188 A u x h1 h2) (@lem3261873 A u x h2)). Qed.
Lemma lem3262190 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262066 A t s u x h1 h2) (fun h3 : False => @lem3261869 A s x h1)). Qed.
Lemma lem3262191 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262190 A t s u x h1 h2) (@lem3261869 A s x h1)). Qed.
Lemma lem3262192 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262043 A t s u x h1 h2) (fun h3 : False => @lem3261859 A s x h1)). Qed.
Lemma lem3262193 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262192 A t s u x h1 h2) (@lem3261859 A s x h1)). Qed.
Lemma lem3262194 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262020 A t s u x h1 h2) (fun h3 : False => @lem3261853 A s x h1)). Qed.
Lemma lem3262195 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262194 A t s u x h1 h2) (@lem3261853 A s x h1)). Qed.
Lemma lem3262196 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262195 A t s u x h1 h2) (fun h3 : False => @lem3261851 A s x h1)). Qed.
Lemma lem3262197 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262196 A t s u x h1 h2) (@lem3261851 A s x h1)). Qed.
Lemma lem3262198 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3261997 A t x h1 h2) (fun h3 : False => @lem3261845 A t x h1)). Qed.
Lemma lem3262199 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262198 A t x h1 h2) (@lem3261845 A t x h1)). Qed.
Lemma lem3262200 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3262199 A t x h1 h2) (fun h3 : False => @lem3261841 A t x h2)). Qed.
Lemma lem3262201 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262200 A t x h1 h2) (@lem3261841 A t x h2)). Qed.
Lemma lem3262202 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3261974 A t s u x h1 h2) (fun h3 : False => @lem3261837 A s x h1)). Qed.
Lemma lem3262203 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262202 A t s u x h1 h2) (@lem3261837 A s x h1)). Qed.
Lemma lem3262204 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3261951 A t x h1 h2) (fun h3 : False => @lem3261829 A t x h1)). Qed.
Lemma lem3262205 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262204 A t x h1 h2) (@lem3261829 A t x h1)). Qed.
Lemma lem3262206 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3262205 A t x h1 h2) (fun h3 : False => @lem3261825 A t x h2)). Qed.
Lemma lem3262207 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262206 A t x h1 h2) (@lem3261825 A t x h2)). Qed.
Lemma lem3262208 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3261928 A t s u x h1 h2) (fun h3 : False => @lem3261821 A s x h1)). Qed.
Lemma lem3262209 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262208 A t s u x h1 h2) (@lem3261821 A s x h1)). Qed.
Lemma lem3262210 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262209 A t s u x h1 h2) (fun h3 : False => @lem3261819 A s x h1)). Qed.
Lemma lem3262211 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262210 A t s u x h1 h2) (@lem3261819 A s x h1)). Qed.
Lemma lem3262212 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262183 A s u x h1 h2) (fun h3 : False => @lem3261797 A s x h1)). Qed.
Lemma lem3262213 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : False.
Proof. exact (EQ_MP (@lem3262212 A s u x h1 h2) (@lem3261797 A s x h1)). Qed.
Lemma lem3262214 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262185 A s t x h1 h2) (fun h3 : False => @lem3261769 A s x h1)). Qed.
Lemma lem3262215 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : False.
Proof. exact (EQ_MP (@lem3262214 A s t x h1 h2) (@lem3261769 A s x h1)). Qed.
Lemma lem3262216 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3262189 A u x h1 h2) (fun h3 : False => @lem3261753 A u x h1)). Qed.
Lemma lem3262217 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262216 A u x h1 h2) (@lem3261753 A u x h1)). Qed.
Lemma lem3262218 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3262217 A u x h1 h2) (fun h3 : False => @lem3261749 A u x h2)). Qed.
Lemma lem3262219 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262218 A u x h1 h2) (@lem3261749 A u x h2)). Qed.
Lemma lem3262220 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262191 A t s u x h1 h2) (fun h3 : False => @lem3261741 A s x h1)). Qed.
Lemma lem3262221 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262220 A t s u x h1 h2) (@lem3261741 A s x h1)). Qed.
Lemma lem3262222 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262193 A t s u x h1 h2) (fun h3 : False => @lem3261721 A s x h1)). Qed.
Lemma lem3262223 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262222 A t s u x h1 h2) (@lem3261721 A s x h1)). Qed.
Lemma lem3262224 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262197 A t s u x h1 h2) (fun h3 : False => @lem3261709 A s x h1)). Qed.
Lemma lem3262225 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262224 A t s u x h1 h2) (@lem3261709 A s x h1)). Qed.
Lemma lem3262226 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262225 A t s u x h1 h2) (fun h3 : False => @lem3261705 A s x h1)). Qed.
Lemma lem3262227 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262226 A t s u x h1 h2) (@lem3261705 A s x h1)). Qed.
Lemma lem3262228 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3262201 A t x h1 h2) (fun h3 : False => @lem3261693 A t x h1)). Qed.
Lemma lem3262229 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262228 A t x h1 h2) (@lem3261693 A t x h1)). Qed.
Lemma lem3262230 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3262229 A t x h1 h2) (fun h3 : False => @lem3261685 A t x h2)). Qed.
Lemma lem3262231 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262230 A t x h1 h2) (@lem3261685 A t x h2)). Qed.
Lemma lem3262232 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262203 A t s u x h1 h2) (fun h3 : False => @lem3261677 A s x h1)). Qed.
Lemma lem3262233 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262232 A t s u x h1 h2) (@lem3261677 A s x h1)). Qed.
Lemma lem3262234 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3262207 A t x h1 h2) (fun h3 : False => @lem3261661 A t x h1)). Qed.
Lemma lem3262235 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262234 A t x h1 h2) (@lem3261661 A t x h1)). Qed.
Lemma lem3262236 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3262235 A t x h1 h2) (fun h3 : False => @lem3261653 A t x h2)). Qed.
Lemma lem3262237 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262236 A t x h1 h2) (@lem3261653 A t x h2)). Qed.
Lemma lem3262238 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262211 A t s u x h1 h2) (fun h3 : False => @lem3261645 A s x h1)). Qed.
Lemma lem3262239 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262238 A t s u x h1 h2) (@lem3261645 A s x h1)). Qed.
Lemma lem3262240 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262239 A t s u x h1 h2) (fun h3 : False => @lem3261641 A s x h1)). Qed.
Lemma lem3262241 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262240 A t s u x h1 h2) (@lem3261641 A s x h1)). Qed.
Lemma lem3262242 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262213 A s u x h1 h2) (fun h3 : False => @lem3261797 A s x h1)). Qed.
Lemma lem3262243 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s u x) : False.
Proof. exact (EQ_MP (@lem3262242 A s u x h1 h2) (@lem3261797 A s x h1)). Qed.
Lemma lem3262244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262215 A s t x h1 h2) (fun h3 : False => @lem3261769 A s x h1)). Qed.
Lemma lem3262245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term32 A s t x) : False.
Proof. exact (EQ_MP (@lem3262244 A s t x h1 h2) (@lem3261769 A s x h1)). Qed.
Lemma lem3262246 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3262219 A u x h1 h2) (fun h3 : False => @lem3261753 A u x h1)). Qed.
Lemma lem3262247 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262246 A u x h1 h2) (@lem3261753 A u x h1)). Qed.
Lemma lem3262248 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3262247 A u x h1 h2) (fun h3 : False => @lem3261749 A u x h2)). Qed.
Lemma lem3262249 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3262248 A u x h1 h2) (@lem3261749 A u x h2)). Qed.
Lemma lem3262250 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262221 A t s u x h1 h2) (fun h3 : False => @lem3261741 A s x h1)). Qed.
Lemma lem3262251 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262250 A t s u x h1 h2) (@lem3261741 A s x h1)). Qed.
Lemma lem3262252 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262223 A t s u x h1 h2) (fun h3 : False => @lem3261721 A s x h1)). Qed.
Lemma lem3262253 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262252 A t s u x h1 h2) (@lem3261721 A s x h1)). Qed.
Lemma lem3262254 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262227 A t s u x h1 h2) (fun h3 : False => @lem3261709 A s x h1)). Qed.
Lemma lem3262255 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262254 A t s u x h1 h2) (@lem3261709 A s x h1)). Qed.
Lemma lem3262256 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262255 A t s u x h1 h2) (fun h3 : False => @lem3261705 A s x h1)). Qed.
Lemma lem3262257 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262256 A t s u x h1 h2) (@lem3261705 A s x h1)). Qed.
Lemma lem3262258 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3262231 A t x h1 h2) (fun h3 : False => @lem3261693 A t x h1)). Qed.
Lemma lem3262259 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262258 A t x h1 h2) (@lem3261693 A t x h1)). Qed.
Lemma lem3262260 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3262259 A t x h1 h2) (fun h3 : False => @lem3261685 A t x h2)). Qed.
Lemma lem3262261 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262260 A t x h1 h2) (@lem3261685 A t x h2)). Qed.
Lemma lem3262262 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262233 A t s u x h1 h2) (fun h3 : False => @lem3261677 A s x h1)). Qed.
Lemma lem3262263 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262262 A t s u x h1 h2) (@lem3261677 A s x h1)). Qed.
Lemma lem3262264 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3262237 A t x h1 h2) (fun h3 : False => @lem3261661 A t x h1)). Qed.
Lemma lem3262265 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262264 A t x h1 h2) (@lem3261661 A t x h1)). Qed.
Lemma lem3262266 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3262265 A t x h1 h2) (fun h3 : False => @lem3261653 A t x h2)). Qed.
Lemma lem3262267 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3262266 A t x h1 h2) (@lem3261653 A t x h2)). Qed.
Lemma lem3262268 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262241 A t s u x h1 h2) (fun h3 : False => @lem3261645 A s x h1)). Qed.
Lemma lem3262269 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262268 A t s u x h1 h2) (@lem3261645 A s x h1)). Qed.
Lemma lem3262270 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : (term79 A s x) = False.
Proof. exact (prop_ext (fun h3 : term79 A s x => @lem3262269 A t s u x h1 h2) (fun h3 : False => @lem3261641 A s x h1)). Qed.
Lemma lem3262271 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262270 A t s u x h1 h2) (@lem3261641 A s x h1)). Qed.
Lemma lem3262272 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s u x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3261615 A t s u x h2) (fun h0 : term79 A s x => @lem3262243 A s u x h0 h1) (fun h0 : term56 A t u x => @lem3262181 A t s u x h0 h1)). Qed.
Lemma lem3262273 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term32 A s t x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3261615 A t s u x h2) (fun h0 : term79 A s x => @lem3262245 A s t x h0 h1) (fun h0 : term56 A t u x => @lem3262135 A u s t x h0 h1)). Qed.
Lemma lem3262274 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3261614 A t s u x h1) (fun h0 : term32 A s t x => @lem3262273 A t s u x h0 h1) (fun h0 : term32 A s u x => @lem3262272 A t s u x h0 h1)). Qed.
Lemma lem3262275 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) (h3 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261597 A t s u x h3) (fun h0 : term79 A s x => @lem3262251 A t s u x h0 h3) (fun h0 : term79 A t x => @lem3262249 A u x h1 h2)). Qed.
Lemma lem3262276 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A s x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261597 A t s u x h2) (fun h0 : term79 A s x => @lem3262257 A t s u x h1 h2) (fun h0 : term79 A t x => @lem3262253 A t s u x h1 h2)). Qed.
Lemma lem3262277 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : u x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261596 A t s u x h2) (fun h0 : term79 A s x => @lem3262276 A t s u x h0 h2) (fun h0 : term79 A u x => @lem3262275 A t s u x h0 h1 h2)). Qed.
Lemma lem3262278 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261597 A t s u x h2) (fun h0 : term79 A s x => @lem3262263 A t s u x h0 h2) (fun h0 : term79 A t x => @lem3262261 A t x h0 h1)). Qed.
Lemma lem3262279 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261597 A t s u x h2) (fun h0 : term79 A s x => @lem3262271 A t s u x h0 h2) (fun h0 : term79 A t x => @lem3262267 A t x h0 h1)). Qed.
Lemma lem3262280 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : t x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261596 A t s u x h2) (fun h0 : term79 A s x => @lem3262279 A t s u x h1 h2) (fun h0 : term79 A u x => @lem3262278 A t s u x h1 h2)). Qed.
Lemma lem3262281 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3261598 A t s u x h1) (fun h0 : t x => @lem3262280 A t s u x h0 h1) (fun h0 : u x => @lem3262277 A t s u x h0 h1)). Qed.
Lemma lem3262282 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : False.
Proof. exact (or_elim (@lem3261591 A t s u x h1) (fun h0 : term74 A t s u x => @lem3262281 A t s u x h0) (fun h0 : term71 A t s u x => @lem3262274 A t s u x h0)). Qed.
Lemma lem3262283 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : (term54 A t s u x) = False.
Proof. exact (prop_ext (fun h2 : term54 A t s u x => @lem3262282 A t s u x h1) (fun h2 : False => @lem3261425 A t s u x h1)). Qed.
Lemma lem3262284 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : False.
Proof. exact (EQ_MP (@lem3262283 A t s u x h1) (@lem3261425 A t s u x h1)). Qed.
Lemma lem3262285 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : term53 A t s u x.
Proof. exact (fun h0 : term54 A t s u x => @lem3262284 A t s u x h0). Qed.
Lemma lem3262286 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term27 A s t u x) = (term35 A t s u x).
Proof. exact (EQ_MP (@lem3261424 A t s u x) (@lem3262285 A t s u x)). Qed.
Lemma lem3262291 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term38 A t s u.
Proof. exact (fun x : A => @lem3262286 A t s u x). Qed.
Lemma lem3262296 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term40 A t s.
Proof. exact (fun u : A -> Prop => @lem3262291 A t s u). Qed.
Lemma lem3262301 {A : Type'} (s : A -> Prop) : term42 A s.
Proof. exact (fun t : A -> Prop => @lem3262296 A t s). Qed.
Lemma lem3262306 {A : Type'} : term44 A.
Proof. exact (fun s : A -> Prop => @lem3262301 A s). Qed.
Lemma lem3262307 {A : Type'} : term46 A.
Proof. exact (EQ_MP (@lem3261420 A) (@lem3262306 A)). Qed.
Lemma lem3262309 {A : Type'} : term46 A.
Proof. exact (@lem3261308 A (@lem3262307 A)). Qed.
Lemma lem3262310 {A : Type'} (h1 : term47 A) : False.
Proof. exact (@lem3262309 A (@lem3261292 A h1)). Qed.
Lemma lem3262311 {A : Type'} (h1 : term47 A) : (term47 A) = False.
Proof. exact (prop_ext (fun h2 : term47 A => @lem3262310 A h1) (fun h2 : False => @lem3261292 A h1)). Qed.
Lemma lem3262312 {A : Type'} (h1 : term47 A) : False.
Proof. exact (EQ_MP (@lem3262311 A h1) (@lem3261292 A h1)). Qed.
Lemma lem3262313 {A : Type'} : term46 A.
Proof. exact (fun h0 : term47 A => @lem3262312 A h0). Qed.
Lemma lem3262314 {A : Type'} : term44 A.
Proof. exact (EQ_MP (@lem3261291 A) (@lem3262313 A)). Qed.
Lemma lem3262315 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3261287 A) (@lem3262314 A)). Qed.
Lemma lem3262316 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3261148 A) (@lem3262315 A)). Qed.
